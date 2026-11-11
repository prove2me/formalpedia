-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_48
-- name    : SparseTensorInj.Certify.lemma_48
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:28.372352+00:00
-- url     : https://prove2.me/theorems/e8c01bd9-e795-4e2a-abbf-b4ef2a557e71
-- title:
--   Lemma 48 — correctness of the odd-order certificate (9)
-- statement:
--   Let $q\ge1$ and let $T$ be a symmetric order-$(2q+1)$ tensor over $\mathbb R^n$ (any $n$). Then
--   $$\|T\|_{\mathrm{inj}}\le u(T)=\|T-T^\circ\|_F+\frac{(2q+1)!}{2\cdot q!}\sqrt{\|M\|_{\mathrm{op}}+2d_{\max}},$$
--   with $T^\circ$, $M$ and $d_{\max}$ as in Construction 47. This is the correctness half of Proposition 44: the certificate is a valid upper bound for every symmetric tensor, random or not.
--
--   Differences from the source:
--
--   - reading: the constant (2q + 1)!/2q! in eq. (9) → (2q+1)!/(2·q!); reason: the proof of Lemma 48 (p. 27) derives exactly this constant (‖z‖² ≤ 1/q!); the (2q)! reading changes the certificate for q ≥ 2
--   - encoding: a fixed natural order ≺ on [n], with J_e, K_e read off the ≺-increasing ordering of e → the order of Fin n; J_e, K_e are the images of positions 1..q and q+1..2q under Finset.orderEmbOfFin; reason: the natural order of [n]
--   - encoding: ‖T‖_inj = max over unit vectors x of |⟨T, x^{⊗k}⟩| → the real supremum ⨆ over {x : Fin n → ℝ | Σ x_i² = 1}; reason: the set of values is bounded and the maximum is attained for n ≥ 1; for n = 0 (empty sphere) the value is 0 and the claim is trivial
--   - encoding: indices in [n] = {1,…,n}; the k-element subsets [n]_k → Fin n (0-based); KSubset n k = {e : Finset (Fin n) // e.card = k}; reason: relabelling of the index set; same instances
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 26, Lemma 48

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_OddCertificate

namespace SparseTensorInj.Certify

/-- Lemma 48 (p. 26): for every symmetric order-`(2q+1)` tensor `T` (`q ≥ 1`),
`‖T‖_inj ≤ u(T)` with `u(T) = ‖T − T°‖_F + ((2q+1)!/(2·q!)) √(‖M‖_op + 2 d_max)` (eq. (9)). -/
theorem lemma_48 (q n : ℕ) (hq : 1 ≤ q) (T : Tensor (2 * q + 1) n) (hT : IsSymmetric T) :
    injNorm T ≤ oddCert T := by sorry

end SparseTensorInj.Certify
