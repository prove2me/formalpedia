-- Prove2me | Theorems.Thm_RestrictedDec_probe_scheme_not_prechallenge_secure
-- name    : RestrictedDec.probe_scheme_not_prechallenge_secure
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:55:38.698503+00:00
-- url     : https://prove2.me/theorems/483d8d37-fed5-401d-88f9-e1bdb79506a7
-- title:
--   Proof of Corollary 2 — the probe scheme is not in $\mathrm{Sec}^{na}(q_T)$
-- statement:
--   Let $n$ be a public polynomial message length, $S_\lambda,T_\lambda$ uniformly computable coordinate sets with $T_\lambda\setminus S_\lambda\neq\emptyset$ for all sufficiently large $\lambda$, and $E$ an efficient scheme over $\{0,1\}^{n(\lambda)}$ with ordinary correctness. Then
--
--   $$\text{probe scheme}\notin\mathrm{Sec}^{na}(q_T).$$
--
--   Querying $q_T$ on every probe reveals the encoded secret key, since $q_T(0^n)\neq q_T(e_j)$; the attacker then decrypts a challenge encryption of two fixed distinct messages, and ordinary correctness makes its advantage non-negligible.
--
--   Differences from the source:
--   - generalization: E IND-CCA2 secure, and S_λ ≠ ∅ eventually → E efficient with ordinary correctness (Correct n E); no hypothesis on S; reason: the attack uses only correctness and T_λ \ S_λ ≠ ∅; an IND-CCA2 scheme is correct by definition
--   - reading: n(λ) polynomially bounded → PolyParam n: polynomially bounded and 1^{n(λ)} computable from 1^λ in polynomial time; reason: p.13 assumes the common message space has efficiently found messages; the constructions need 0ⁿ, e_i, e_j
--   - encoding: S_λ, T_λ ⊆ [n(λ)] uniformly computable → UniformSets: S λ ⊆ {1, …, n λ} and its characteristic vector computed from 1^λ in polynomial time; reason: the paper's uniformity convention, §2.3 p.15
--   - reading: public-key encryption scheme over {0,1}^{n(λ)} → PKE with PKE.IsScheme n (polynomial-time algorithms, Dec into M_⊥); reason: App. A.1, p.29 and the efficiency of PKE schemes; kept apart from Sec
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: probes (1, k) over the bits of a fixed, efficiently decodable encoding of sk_E → probe index k in unary; η(sk) = selfDelim sk followed by zeros; reason: a fixed encoding whose set of probes does not depend on the key
--   - encoding: positions i ∈ S_λ, j ∈ T_λ \ S_λ chosen where they exist → i, j = least element, default 0 with e_0 = 0ⁿ at the other λ; reason: asymptotic notions ignore the finitely many λ where the sets are empty; the witnesses stay single uniform schemes
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22

import Mathlib
import Definitions.Def_RestrictedDec_PolyParam
import Definitions.Def_RestrictedDec_UniformSets
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_Correct
import Definitions.Def_RestrictedDec_Sec
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_qCoord
import Definitions.Def_RestrictedDec_probeScheme
open QAlgorithms.Complexity
open Filter
set_option autoImplicit false

namespace RestrictedDec

/-- **The probe scheme is not pre-challenge `q_T`-secure** (proof of Corollary 2, p.22). Let `n`
be a public polynomial message length, `S, T` uniformly computable coordinate sets with
`T_λ \ S_λ ≠ ∅` for all sufficiently large `λ`, and `E` an efficient scheme over `{0,1}^{n(λ)}`
with ordinary correctness. Then the probe scheme built from `E` is not in `Sec^na(q_T)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.22
("In the pre-challenge qT experiment, however, querying qT on every probe reveals the encoded
secret key … Ordinary correctness makes its advantage non-negligible"). -/
theorem probe_scheme_not_prechallenge_secure (n : ℕ → ℕ) (hn : PolyParam n)
    (S T : ℕ → Finset ℕ) (hS : UniformSets n S) (hT : UniformSets n T)
    (hTS : ∀ᶠ lam in atTop, (T lam \ S lam).Nonempty) (E : PKE) (hE : E.IsScheme n)
    (hcor : Correct n E) :
    ¬ Sec .na n (famObs (qCoord T)) (probeScheme E n S T) := by sorry

end RestrictedDec
