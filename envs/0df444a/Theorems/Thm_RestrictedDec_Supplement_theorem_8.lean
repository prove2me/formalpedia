-- Prove2me | Theorems.Thm_RestrictedDec_Supplement_theorem_8
-- name    : RestrictedDec.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:41:36.9046+00:00
-- url     : https://prove2.me/theorems/8db49ee5-8205-4e51-8ff2-4cafa95f9281
-- title:
--   Theorem 8 — the pre-challenge Naor–Yung compiler is in $\mathrm{Sec}^{na}(q)$
-- statement:
--   Let $M$ be a common message space with efficiently recognizable valid plaintexts and $q$ a public observation with $\mathrm{Valid}_q$, $\mathrm{Rep}_q$ and label length $\ell(\lambda)$. Assume
--
--   1. $R$ is an efficient residual scheme over $M$ with IND-CPA security and ordinary correctness;
--   2. $L$ is an efficient IND-CPA-secure label scheme over $\{0,1\}^{\ell(\lambda)}$ with keywise correctness (KC);
--   3. $N$ is an efficient NIZK for the relation (B.1) that is perfectly complete, computationally sound and adaptively one-theorem zero knowledge, and whose simulator produces accepting proofs for well-formed statements (Definition 11).
--
--   Then the encryption scheme (B.1)–(B.2) satisfies $\mathrm{IND}^{na}_{\mathcal F_q}$ security, where $\mathcal F_q=\{g\circ q: g\text{ an efficient public postprocessing}\}$:
--   $$\Gamma_q\in\mathrm{Sec}^{na}(q).$$
--
--   The proof certifies only that the two label ciphertexts agree on a valid label, not that the residual ciphertext matches it; normalization makes every permitted answer a function of the certified label.
--
--   Differences from the source:
--   - encoding: keys, messages, ciphertexts, labels, M_⊥, coins, PPT adversaries and reductions → bit strings with tuple codes, Option Str (none = ⊥), explicit uniform coin vectors, uniform reactive machines with a polynomial-time step function (RestrictedDec.Adversary); reason: the model of the published base mission; same instances
--   - encoding: Sec^t(q) = Sec^t(F_q), F_q = {g ∘ q : g an admissible circuit / efficient public postprocessing} → SecM t M (famObs q); reason: the published famObs is the class of §2.3, p.14
--   - encoding: PPT primitives (R, L, I, P, S, N, q, samplers) → separate efficiency hypotheses (IsSchemeM, IsEfficient, IsPublic, IsObsMap); reason: the paper's PPT convention; the reductions run these algorithms
--   - reading: efficient recognition of valid plaintexts; perfect completeness of the NIZK → hypotheses Recognizable M and N.Complete; reason: standing assumptions of App. B.1, p.35 ('efficient recognition of valid plaintexts'; 'Both constructions require perfect completeness')
--   - encoding: a label scheme L encrypting ℓ(λ)-bit strings; the label length ℓ(λ) of q → L a PKE efficient and IND-CPA over {0,1}^{ℓ(λ)}, with ℓ the length of q on M_⊥; reason: App. B.1, p.35
--   - encoding: Coins_L, a publicly recognizable set of allowed label randomness → every encryption coin vector of L; r ∈ Coins_L in the relation is |r| = encCoins_L(λ); reason: honest label encryption draws its coins uniformly from all coin vectors, so they are all allowed
--   - encoding: the ciphertext and statement tuples; malformed ciphertexts → canonical tuple codes; the secret key also stores pk₀, pk₁, crs; reason: decryption needs them to form and verify the statement
--   - reading: a simulator producing accepting proofs for well-formed statements in the hybrid distributions → simulated-proof acceptance (Definition 11) for every well-formed statement (x a 5-tuple); reason: App. A.4, p.34: 'Section B.2 uses … the ability of SimProve to generate an accepting proof for an arbitrary statement under the simulated CRS'
--   - encoding: the common message space → hypothesis MsgSpace.Found M; reason: standing assumption of §2.1, p.13
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 8, p.37; (B.1)–(B.2), pp.36–37

import Mathlib
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_Supplement_MsgSpace
import Definitions.Def_RestrictedDec_Supplement_IsSchemeM
import Definitions.Def_RestrictedDec_Supplement_SecM
import Definitions.Def_RestrictedDec_Supplement_INDCPAM
import Definitions.Def_RestrictedDec_Supplement_kcFail
import Definitions.Def_RestrictedDec_Supplement_nyPre
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- **Theorem 8** (the pre-challenge Naor–Yung compiler is pre-challenge `q`-secure). Let `M` be a
common message space with efficiently recognizable valid plaintexts, and `q` a public observation
with `Valid_q`, `Rep_q` and label length `ℓ(λ)`. Let `R` be an efficient, IND-CPA-secure,
ordinarily correct residual scheme over `M`; `L` an efficient IND-CPA-secure label scheme over
`{0,1}^{ℓ(λ)}` with keywise correctness (KC); and `N` an efficient NIZK for the relation (B.1) with
perfect completeness, computational soundness, adaptive one-theorem zero knowledge, and
simulated-proof acceptance for well-formed statements. Then the encryption scheme (B.1)–(B.2) is in
`Sec^na(𝓕_q)`, `𝓕_q = {g ∘ q : g an efficient public postprocessing}`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 8, p.37; construction,
pp.36–37; the requirements of App. B.1, p.35; Definitions 2–4, 8–11.

**Formalization Note.** `𝓕_q` is `famObs q` (postprocessing by admissible circuits, §2.3, p.14).
Simulated-proof acceptance is Definition 11 for the instance space `wfB1`. -/
theorem theorem_8 (M : ℕ → Str → Prop) (hM : MsgSpace.Found M) (hMrec : Recognizable M)
    (o : Obs) (ho : o.IsPublic M) (ℓ : ℕ → ℕ)
    (hℓ : ∀ lam (x : Option Str), (∀ m, x = some m → M lam m) → (o.q lam x).length = ℓ lam)
    (R : PKE) (hR : IsSchemeM M R) (hRcpa : INDCPAM M R) (hRcor : CorrectM M R)
    (L : PKE) (hL : IsSchemeM (fun lam y => y.length = ℓ lam) L)
    (hLcpa : INDCPAM (fun lam y => y.length = ℓ lam) L) (hLkc : KeywiseCorrect L ℓ)
    (N : NIZK) (hN : N.IsEfficient) (hNc : N.Complete (relB1 L o)) (hNs : N.Sound (relB1 L o))
    (hNzk : N.ZK (relB1 L o)) (hNacc : N.SimAccept wfB1) :
    SecM .na M (famObs o.q) (nyPre M o R L N) := by sorry

end Supplement

end RestrictedDec
