-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_quadraticSelfadjointRepresentation
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.quadraticSelfadjointRepresentation
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:47:21.763283+00:00
-- url     : https://prove2.me/theorems/d4bf8847-5433-45b6-a444-b78c801e932c
-- title:
--   Appendix B, Claim A 2: selfadjoint representation
-- statement:
--   Let $H$ be a complete real Hilbert space of arbitrary dimension and let $\beta$ be the diagonal of a bounded symmetric real bilinear form. Then there exists a unique bounded selfadjoint real linear operator $B:H\to H$ such that
--   $$\langle v,Bv\rangle=\beta(v)\qquad\text{for every }v\in H.$$
--   The form may have either sign. Completeness and the real scalar field are retained.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 36, Appendix B, Claim A 2: selfadjoint representation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Appendix B, Claim A 2, PDF p.36: unique bounded selfadjoint
representation on a complete real Hilbert space of arbitrary dimension. -/
theorem quadraticSelfadjointRepresentation {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (beta : H → ℝ)
    (hbeta : IsBoundedQuadratic beta) :
    ∃! B : H →L[ℝ] H, IsSelfAdjoint B ∧ ∀ v, inner ℝ v (B v) = beta v := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
