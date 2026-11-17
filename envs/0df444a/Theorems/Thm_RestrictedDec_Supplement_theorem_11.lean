-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_11
-- name    : RestrictedDec.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:44:23.141195+00:00
-- url     : https://prove2.me/theorems/96f47ea0-71dd-48dd-bb2a-6178d6b91258
-- title:
--   Theorem 11 — the adaptive Naor–Yung scheme $\Pi_q\notin\mathrm{Sec}^{ad}(r)$; success $\ge1-\delta_R-2\delta_L-\mathrm{negl}$ given the sampler succeeds
-- statement:
--   Let $M$ be a common message space, $q$ an observation with the two public conditions of §2.3 and label length $\ell(\lambda)$, and $r$ any uniformly efficient map on decryption outputs. Let $R$ be an efficient, ordinarily correct residual scheme over $M$; $L$ an efficient label scheme over $\{0,1\}^{\ell(\lambda)}$ with (KC); $N$ an efficient, perfectly complete NIZK for (B.4); and $S$ an efficient, correct, strongly unforgeable one-time signature. Suppose a uniform PPT sampler, run independently of the generated keys, finds valid distinct equal-length $m_0,m_1$ with
--   $$q(m_0)=q(m_1),\qquad r(m_0)\neq r(m_1)$$
--   with non-negligible probability on infinitely many security parameters. Then
--
--   1. the signed scheme $\Pi_q$ is not in $\mathrm{Sec}^{ad}(r)$;
--   2. there are a uniform PPT attacker $A$ and a negligible $\nu$ such that, for every nonnegative function $\delta_R$ bounding the honest decryption error of $R$ (Definition 3), every $\lambda$ and every coin vector $\rho$ on which the sampler succeeds, the attacker run with $\rho$ as its sampler coins guesses the challenge bit of the adaptive $\mathcal F_r$ experiment correctly with probability at least
--   $$1-\delta_R(\lambda)-2\delta_L(\lambda)-\nu(\lambda).$$
--
--   The proof constrains only the labels, so a fresh, independently signed ciphertext can reuse the challenge's residual component; a finer oracle then reveals the residual message.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - generalization: conditional on the sampler succeeding, the attacker guesses correctly with probability at least 1 − δ_R − 2δ_L − negl(λ) → the bound for each successful coin vector ρ of the sampler, the attacker started with ρ as its state, with one negligible ν uniform in ρ, λ and δ_R; reason: averaging the pointwise bound over the successful ρ gives the conditional probability
--   - generalization: the standing assumptions of App. B.1 on the construction (CPA security of R and L, the NIZK's soundness, zero knowledge and simulation soundness, efficient recognition of plaintexts) → only the properties the attack uses: correctness of R, (KC) of L, NIZK completeness, signature correctness and strong unforgeability, and efficiency; reason: fewer hypotheses; the paper's setting satisfies them
--   - reading: δ_R (R's honest error) and δ_L in the bound → every nonnegative δ_R with ErrBound M R δ_R (Definition 3), and δ_L = kcFail L ℓ, the exact (KC) failure probability; reason: App. B.1, p.35 ('negligible fixed-message error bound δR'; (KC)); an error bound is a probability bound, and a negative δ_R (possible only where R never errs) would push the lower bound above 1
--   - encoding: a uniform PPT sampler finding the pair with nonnegligible probability on infinitely many security parameters → a uniform PPT Sampler whose success probability is not negligible; reason: a function is non-negligible iff it exceeds some inverse polynomial infinitely often
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 11, p.43; construction Π_q, p.39

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_kcFail
import Definitions.Def_RestrictedDec_Supplement_Sampler
import Definitions.Def_RestrictedDec_Supplement_nyAd
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 11** (adaptive finer-observation separation for the signed Naor–Yung scheme). Let `M`
be a common message space, `q` an observation with the two public conditions of §2.3 and label
length `ℓ(λ)`, and `r` any uniformly efficient map on decryption outputs. Let `R` be an efficient,
ordinarily correct residual scheme over `M`; `L` an efficient label scheme over `{0,1}^{ℓ(λ)}`
with (KC); `N` an efficient, perfectly complete NIZK for (B.4); and `S` an efficient, correct,
strongly unforgeable one-time signature. Suppose a uniform PPT sampler `W`, run independently of the
generated keys, finds valid distinct equal-length `m₀, m₁` with `q(m₀) = q(m₁)` and
`r(m₀) ≠ r(m₁)` with non-negligible probability on infinitely many security parameters. Then
1. the signed scheme `Π_q` is not in `Sec^ad(r)`;
2. there are a uniform PPT attacker `A`, which reads the sampler's coins `ρ` as its initial
   state, and a negligible `ν` such that, for every nonnegative bound `δ_R` on the honest decryption
   error of `R` (Definition 3), every `λ` and every `ρ` on which the sampler succeeds, `A` guesses the
   challenge bit of `Exp^{IND,ad}_{Π_q,𝓕_r}` correctly with probability at least
   `1 − δ_R(λ) − 2δ_L(λ) − ν(λ)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 11, p.43; construction
`Π_q`, p.39.

**Formalization Note.** "Conditional on the sampler succeeding" is stated for each successful coin
vector `ρ` of the sampler (the attacker run with `ρ` as initial state); averaging over the
successful `ρ` gives the conditional probability. `δ_L` is the exact (KC) failure probability
`kcFail`. -/
theorem theorem_11 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M)
    (o : Obs) (ho : o.IsPublic M) (ℓ : ℕ → ℕ)
    (hℓ : ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) → (o.q lam x).length = ℓ lam)
    (r : ℕ → Option Str → Str) (hr : IsEffMap M r)
    (R : PKE) (hR : IsSchemeM M R) (hRcor : CorrectM M R)
    (L : PKE) (hL : IsSchemeM (fun lam y => y.length = ℓ lam) L) (hLkc : KeywiseCorrect L ℓ)
    (S : OTS) (hS : S.IsEfficient) (hSsuf : S.SUF) (hScor : S.Correct)
    (N : NIZK) (hN : N.IsEfficient) (hNc : N.Complete (relB4 L o))
    (W : Sampler) (hW : W.IsEfficient)
    (hWs : ¬ NoisyOWMPC.Negligible (W.succ fun lam u v => M lam u ∧ M lam v ∧ u ≠ v ∧
      u.length = v.length ∧ o.q lam (some u) = o.q lam (some v) ∧ r lam (some u) ≠ r lam (some v))) :
    ¬ SecM .ad M (famObs r) (nyAd M o R L N S) ∧
    ∃ A : Adversary, A.Valid ∧ ∃ ν : ℕ → ℝ, NoisyOWMPC.Negligible ν ∧
      ∀ δR : ℕ → ℝ, (∀ lam, 0 ≤ δR lam) → ErrBound M R δR → ∀ (lam : ℕ) (ρ : Fin (W.coins lam) → Bool),
        (M lam (W.out lam ρ).1 ∧ M lam (W.out lam ρ).2 ∧ (W.out lam ρ).1 ≠ (W.out lam ρ).2 ∧
          (W.out lam ρ).1.length = (W.out lam ρ).2.length ∧
          o.q lam (some (W.out lam ρ).1) = o.q lam (some (W.out lam ρ).2) ∧
          r lam (some (W.out lam ρ).1) ≠ r lam (some (W.out lam ρ).2)) →
        ENNReal.ofReal (1 - δR lam - 2 * kcFail L ℓ lam - ν lam) ≤
          expINDM .ad M (nyAd M o R L N S) (famObs r) A lam (List.ofFn ρ) true := by sorry

end Supplement

end RestrictedDec
