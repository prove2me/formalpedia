-- Prove2me | Theorems.Thm_RestrictedDec_wrap_scheme_not_adaptive_secure
-- name    : RestrictedDec.wrap_scheme_not_adaptive_secure
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:56:11.313874+00:00
-- url     : https://prove2.me/theorems/a27fab9a-77c6-40c8-9d54-de4a520d58a4
-- title:
--   Proof of Corollary 2 — the wrap scheme is not in $\mathrm{Sec}^{ad}(q_S)$
-- statement:
--   Let $n$ be a public polynomial message length, $S_\lambda$ uniformly computable coordinate sets with $S_\lambda\neq\emptyset$ for all sufficiently large $\lambda$, and $E$ an efficient scheme over $\{0,1\}^{n(\lambda)}$ with ordinary correctness. Then
--
--   $$\text{wrap scheme}\notin\mathrm{Sec}^{ad}(q_S).$$
--
--   An adaptive adversary chooses the challenge messages $(0^n,e_i)$, receives $(0,c^*)$ and queries the distinct ciphertext $(1,c^*)$ under $q_S$; by correctness the answer is $q_S(0^n)$ or $q_S(e_i)$ according to the challenge bit, and these two values differ.
--
--   Differences from the source:
--   - generalization: E IND-CCA1 secure, and T_λ \ S_λ ≠ ∅ eventually → E efficient with ordinary correctness (Correct n E); no hypothesis on T; reason: the attack uses only correctness and S_λ ≠ ∅; an IND-CCA1 scheme is correct by definition
--   - reading: n(λ) polynomially bounded → PolyParam n: polynomially bounded and 1^{n(λ)} computable from 1^λ in polynomial time; reason: p.13 assumes the common message space has efficiently found messages; the constructions need 0ⁿ, e_i, e_j
--   - encoding: S_λ, T_λ ⊆ [n(λ)] uniformly computable → UniformSets: S λ ⊆ {1, …, n λ} and its characteristic vector computed from 1^λ in polynomial time; reason: the paper's uniformity convention, §2.3 p.15
--   - reading: public-key encryption scheme over {0,1}^{n(λ)} → PKE with PKE.IsScheme n (polynomial-time algorithms, Dec into M_⊥); reason: App. A.1, p.29 and the efficiency of PKE schemes; kept apart from Sec
--   - reading: every PPT adversary → every uniform reactive machine with a polynomial-time step function and polynomial bounds on coins, state, moves and activations; reason: the paper's adversaries are uniform (p.15 'a single PPT attack', p.28 'a uniform adversary')
--   - encoding: positions i ∈ S_λ, j ∈ T_λ \ S_λ chosen where they exist → i, j = least element, default 0 with e_0 = 0ⁿ at the other λ; reason: asymptotic notions ignore the finitely many λ where the sets are empty; the witnesses stay single uniform schemes
--   - encoding: messages, keys, ciphertexts, pairs (β, c), positions in [n] → bit strings Str, (β, c) as β :: c, ⊥ as none, positions numbered from 1; reason: Lean convention; same instances
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.23

import Mathlib
import Definitions.Def_RestrictedDec_PolyParam
import Definitions.Def_RestrictedDec_UniformSets
import Definitions.Def_RestrictedDec_PKE_IsScheme
import Definitions.Def_RestrictedDec_Correct
import Definitions.Def_RestrictedDec_Sec
import Definitions.Def_RestrictedDec_famObs
import Definitions.Def_RestrictedDec_qCoord
import Definitions.Def_RestrictedDec_wrapScheme
open QAlgorithms.Complexity
open Filter
set_option autoImplicit false

namespace RestrictedDec

/-- **The wrap scheme is not adaptively `q_S`-secure** (proof of Corollary 2, p.23). Let `n` be a
public polynomial message length, `S` uniformly computable coordinate sets with `S_λ ≠ ∅` for all
sufficiently large `λ`, and `E` an efficient scheme over `{0,1}^{n(λ)}` with ordinary
correctness. Then the wrap scheme built from `E` is not in `Sec^ad(q_S)`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), proof of Corollary 2, p.23
("An adaptive qS-adversary chooses the challenge messages (0n, ei) and receives (0, c∗). It queries
the distinct ciphertext (1, c∗) under qS. … the scheme is not in Secad(qS)."). -/
theorem wrap_scheme_not_adaptive_secure (n : ℕ → ℕ) (hn : PolyParam n) (S : ℕ → Finset ℕ)
    (hS : UniformSets n S) (hSne : ∀ᶠ lam in atTop, (S lam).Nonempty) (E : PKE)
    (hE : E.IsScheme n) (hcor : Correct n E) :
    ¬ Sec .ad n (famObs (qCoord S)) (wrapScheme E n S) := by sorry

end RestrictedDec
