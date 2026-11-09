-- Prove2me | Theorems.Thm_RestrictedDec_wrap_scheme_prechallenge_secure
-- name    : RestrictedDec.wrap_scheme_prechallenge_secure
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:56:45.87365+00:00
-- url     : https://prove2.me/theorems/ca7e00b6-3d12-4012-98b1-ec3a6f272399
-- title:
--   Proof of Corollary 2 — the wrap scheme is in $\mathrm{Sec}^{na}(q_T)$
-- statement:
--   Let $n$ be a public polynomial message length, $S_\lambda,T_\lambda$ uniformly computable coordinate sets, and $E$ an efficient IND-CCA1-secure scheme over $\{0,1\}^{n(\lambda)}$. Then the wrap scheme built from $E$ is an efficient scheme over $\{0,1\}^{n(\lambda)}$, and
--
--   $$\text{wrap scheme}\in\mathrm{Sec}^{na}(q_T).$$
--
--   Before the challenge, a full CCA1 decryption oracle for $E$ simulates every $q_T$-query of either ciphertext type exactly.
--
--   Differences from the source:
--   - generalization: in the proof, S_λ ≠ ∅ and T_λ \ S_λ ≠ ∅ for all sufficiently large λ → no such hypothesis; reason: the simulation does not use it; with it the statement is the paper's
--   - reading: n(λ) polynomially bounded → PolyParam n: polynomially bounded and 1^{n(λ)} computable from 1^λ in polynomial time; reason: p.13 assumes the common message space has efficiently found messages; the constructions need 0ⁿ, e_i, e_j
--   - encoding: S_λ, T_λ ⊆ [n(λ)] uniformly computable → UniformSets: S λ ⊆ {1, …, n λ} and its characteristic vector computed from 1^λ in polynomial time; reason: the paper's uniformity convention, §2.3 p.15
--   - reading: public-key encryption scheme over {0,1}^{n(λ)} → PKE with PKE.IsScheme n (polynomial-time algorithms, Dec into M_⊥); reason: App. A.1, p.29 and the efficiency of PKE schemes; kept apart from Sec
--   - reading: IND-CCA1 / IND-CCA2 → INDCCA1 = Sec^na(𝓕_id), INDCCA2 = Sec^ad(𝓕_id); reason: §2.2, p.14: the requirements coincide, including ordinary correctness
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: positions i ∈ S_λ, j ∈ T_λ \ S_λ chosen where they exist → i, j = least element, default 0 with e_0 = 0ⁿ at the other λ; reason: asymptotic notions ignore the finitely many λ where the sets are empty; the witnesses stay single uniform schemes
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.23

import Mathlib
import Definitions.Def_RestrictedDec_PolyParam
import Definitions.Def_RestrictedDec_UniformSets
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_INDCCA2
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_qCoord
import Definitions.Def_RestrictedDec_wrapScheme
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- **The wrap scheme is pre-challenge `q_T`-secure** (proof of Corollary 2, p.23). Let `n` be a
public polynomial message length, `S, T` uniformly computable coordinate sets, and `E` an
efficient IND-CCA1-secure scheme over `{0,1}^{n(λ)}`. Then the wrap scheme built from `E` is an
efficient scheme over `{0,1}^{n(λ)}` and belongs to `Sec^na(q_T)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.23
("Before the challenge, a full CCA1 decryption oracle for E simulates every qT-query of either
type exactly, so this scheme belongs to Secna(qT)."). -/
theorem wrap_scheme_prechallenge_secure (n : ℕ → ℕ) (hn : PolyParam n) (S T : ℕ → Finset ℕ)
    (hS : UniformSets n S) (hT : UniformSets n T) (E : PKE) (hE : E.IsScheme n)
    (hcca1 : INDCCA1 n E) :
    (wrapScheme E n S).IsScheme n ∧ Sec .na n (famObs (qCoord T)) (wrapScheme E n S) := by sorry

end RestrictedDec
