-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_10
-- name    : RestrictedDec.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:43:28.641742+00:00
-- url     : https://prove2.me/theorems/9c680fb7-723f-421f-8ba9-42bc14f10ee6
-- title:
--   Theorem 10 — the adaptive Naor–Yung compiler $\Pi_q\in\mathrm{Sec}^{ad}(q)$ with $\mathrm{Gap}\le\epsilon_R+\epsilon_{L,0}+\epsilon_{L,1}+2\epsilon_{ZK}+6\epsilon_{SUF}+6Q\epsilon_{SS}+12\delta_L$
-- statement:
--   Let $M$ be a common message space with efficiently recognizable valid plaintexts and $q$ a public observation with the public algorithms of §2.3 and label length $\ell(\lambda)$. Suppose
--
--   1. $R$ is an efficient residual scheme over $M$, IND-CPA secure and ordinarily correct;
--   2. $L$ is an efficient IND-CPA-secure label scheme over $\{0,1\}^{\ell(\lambda)}$ satisfying (KC) with negligible $\delta_L$;
--   3. $S$ is an efficient, correct, strongly unforgeable one-time signature;
--   4. $N$ is an efficient NIZK for the relation (B.4) with the one-theorem properties of App. A.4: perfect completeness, soundness, adaptive zero knowledge, simulated-proof acceptance and one-theorem simulation soundness for new statements.
--
--   Then $\Pi_q\in\mathrm{Sec}^{ad}(q)$. More precisely, for every uniform PPT adversary $A$ making at most $Q(\lambda)$ functional-decryption queries there are uniform PPT reductions $B_R,B_{L,0},B_{L,1},B_{ZK},B_{SUF},B_{SS}$ such that for every $\lambda$
--   $$\mathrm{Gap}_{\Pi_q,q}(A)\le\epsilon_R+\epsilon_{L,0}+\epsilon_{L,1}+2\epsilon_{ZK}+6\epsilon_{SUF}+6Q\epsilon_{SS}+12\delta_L,\tag{B.5}$$
--   where $\mathrm{Gap}=|\Pr[A\Rightarrow1\mid b=1]-\Pr[A\Rightarrow1\mid b=0]|$ in the adaptive $\mathcal F_q$ game, $\epsilon_R$ and $\epsilon_{L,b}$ are the CPA gaps (Definition 2) of $B_R$ against $R$ and of $B_{L,b}$ against $L$, $\epsilon_{ZK}$ is the zero-knowledge gap (Definition 10) of $B_{ZK}$, $\epsilon_{SUF}$ the forgery probability (Definition 13) of $B_{SUF}$, and $\epsilon_{SS}$ the simulation-soundness success probability (Definition 12) of $B_{SS}$, all at $\lambda$.
--
--   The bound makes the security loss explicit; only the simulation-soundness term grows with the number of queries.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: efficient recognition of valid plaintexts; perfect completeness of the NIZK → hypotheses Recognizable M and N.Complete; reason: standing assumptions of App. B.1, p.35 ('efficient recognition of valid plaintexts'; 'Both constructions require perfect completeness')
--   - encoding: a label scheme L encrypting ℓ(λ)-bit strings; the label length ℓ(λ) of q → L a PKE efficient and IND-CPA over {0,1}^{ℓ(λ)}, with ℓ the length of q on M_⊥; reason: App. B.1, p.35
--   - encoding: Coins_L, a publicly recognizable set of allowed label randomness → every encryption coin vector of L; r ∈ Coins_L in the relation is |r| = encCoins_L(λ); reason: honest label encryption draws its coins uniformly from all coin vectors, so they are all allowed
--   - encoding: the ciphertext and statement tuples; malformed ciphertexts → canonical tuple codes; the secret key also stores pk₀, pk₁, crs; reason: decryption needs them to form and verify the statement
--   - reading: the NIZK satisfies the one-theorem properties above for (B.4) → N.Complete, N.Sound, N.ZK, N.SimAccept (well-formed 6-tuples) and N.SimSound for relB4; reason: Definitions 8–12, App. A.4, pp.33–34 and the requirements of App. B.1, p.35
--   - reading: S is a strongly unforgeable one-time signature scheme → S efficient, strongly unforgeable (Definition 13) and correct (Definition 14); reason: App. A.5, p.34: 'The adaptive compiler uses strong one-time unforgeability and signature correctness'
--   - reading: every PPT adversary making at most Q queries yields PPT reductions with Gap ≤ … (each ϵ the advantage of its reduction) → for every valid A and every Q with QueryBounded A Q there exist valid reductions, one per term, with the inequality at every λ; reason: (B.5), p.40; the advantages use the Gap convention of p.40
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 10 and (B.5), p.40; construction, p.39

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_kcFail
import Definitions.Def_RestrictedDec_Supplement_QueryBounded
import Definitions.Def_RestrictedDec_Supplement_nyAd
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 10** (the adaptive signed Naor–Yung compiler is adaptively `q`-secure, with the
bound (B.5)). Let `M` be a common message space with efficiently recognizable valid plaintexts and
`q` a public observation with the public algorithms of §2.3 and label length `ℓ(λ)`. Suppose `R`
is an efficient, IND-CPA-secure, ordinarily correct residual scheme over `M`; `L` an efficient
IND-CPA-secure label scheme over `{0,1}^{ℓ(λ)}` satisfying (KC) with negligible `δ_L`; `S` an
efficient, correct, strongly unforgeable one-time signature; and `N` an efficient NIZK for the
relation (B.4) with the one-theorem properties of App. A.4 (perfect completeness, soundness,
adaptive zero knowledge, simulated-proof acceptance, one-theorem simulation soundness). Then
1. `Π_q ∈ Sec^ad(q)`;
2. more precisely, for every uniform PPT adversary `A` making at most `Q(λ)` queries there are
   uniform PPT reductions `B_R, B_{L,0}, B_{L,1}, B_ZK, B_SUF, B_SS` such that for every `λ`
   ```
   Gap_{Π_q,q}(A) ≤ ε_R + ε_{L,0} + ε_{L,1} + 2ε_ZK + 6ε_SUF + 6Qε_SS + 12δ_L      (B.5)
   ```
   where `ε_R`, `ε_{L,b}` are the Definition 2 CPA gaps of `B_R` against `R` and of `B_{L,b}`
   against `L`, `ε_ZK` the Definition 10 gap of `B_ZK`, `ε_SUF` the Definition 13 success of
   `B_SUF`, and `ε_SS` the Definition 12 success of `B_SS`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 10 and (B.5), p.40;
construction, p.39; the Gap convention, p.40. -/
theorem theorem_10 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (hMrec : Recognizable M)
    (o : Obs) (ho : o.IsPublic M) (ℓ : ℕ → ℕ)
    (hℓ : ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) → (o.q lam x).length = ℓ lam)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (L : PKE) (hL : IsSchemeM (fun lam y => y.length = ℓ lam) L)
    (hLcpa : INDCPAM (fun lam y => y.length = ℓ lam) L) (hLkc : KeywiseCorrect L ℓ)
    (S : OTS) (hS : S.IsEfficient) (hSsuf : S.SUF) (hScor : S.Correct)
    (N : NIZK) (hN : N.IsEfficient) (hNc : N.Complete (relB4 L o)) (hNs : N.Sound (relB4 L o))
    (hNzk : N.ZK (relB4 L o)) (hNacc : N.SimAccept wfB4) (hNss : N.SimSound (relB4 L o)) :
    SecM .ad M (famObs o.q) (nyAd M o R L N S) ∧
    ∀ A : Adversary, A.Valid → ∀ Q : ℕ → ℕ,
      QueryBounded .ad M (nyAd M o R L N S) (famObs o.q) A Q →
      ∃ BR BL0 BL1 BZK BSUF BSS : Adversary, BR.Valid ∧ BL0.Valid ∧ BL1.Valid ∧ BZK.Valid ∧
        BSUF.Valid ∧ BSS.Valid ∧ ∀ lam : ℕ,
          gapM .ad M (nyAd M o R L N S) (famObs o.q) A lam ≤
            advCPAM M R BR lam + advCPAM (fun lam y => y.length = ℓ lam) L BL0 lam +
            advCPAM (fun lam y => y.length = ℓ lam) L BL1 lam + 2 * N.zkGap (relB4 L o) BZK lam +
            6 * S.sufAdv BSUF lam + 6 * (Q lam : ℝ) * N.ssAdv (relB4 L o) BSS lam +
            12 * kcFail L ℓ lam := by sorry

end Supplement

end RestrictedDec
