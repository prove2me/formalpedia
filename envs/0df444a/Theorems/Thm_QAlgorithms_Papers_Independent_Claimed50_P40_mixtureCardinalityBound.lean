-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_mixtureCardinalityBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.mixtureCardinalityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:49:12.16389+00:00
-- url     : https://prove2.me/theorems/ebad356b-30ec-4959-a554-c4e96bb6d72a
-- title:
--   Cardinality bounds for rate-dominating channel-state mixtures
-- statement:
--   Fix the finite-dimensional independent-sender channel and commuting receiver accesses of Theorem 3, with $s,r\ge1$. Let $R\in\mathbb R_{\ge0}^s$ admit a finite mixture of product-input channel states satisfying every receiver and subset rate inequality
--   $$
--   \sum_{i\in J}R_i\le\sum_uq_uI_{\gamma_u}(X(J):Y_j\mid X(J^c)).
--   $$
--   There is another such mixture, for the same channel and target rates, with
--   $$
--   |\operatorname{supp}q|\le r(2^s-1).
--   $$
--   If $r=1$, the stronger bound is
--   $$
--   |\operatorname{supp}q|\le s.
--   $$
--   Zero weights and repeated channel states are allowed, so witnesses can be padded to exactly these many indexed entries. The assertion preserves domination of the target rate sums; it does not demand equality of every information coordinate of the old and new mixtures. This supplies finite descriptions for the outer rate region.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 4, Remark 5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark 5, PDF p.4: a rate-dominating mixture can be padded to the stated support
bound; it need not reproduce all information coordinates. The single-receiver bound
is s, and the general bound is r*(2^s-1). -/
theorem mixtureCardinalityBound {s r : ℕ} {C : ClassicalChannel s} (N : Network C r)
    (R : Fin s → ℝ) (hR : ∀ i, 0 ≤ R i) :
    ((∃ k : ℕ, MixtureDominates N R k) → MixtureDominates N R (r * (2 ^ s - 1))) ∧
    (r = 1 → (∃ k : ℕ, MixtureDominates N R k) → MixtureDominates N R s) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
