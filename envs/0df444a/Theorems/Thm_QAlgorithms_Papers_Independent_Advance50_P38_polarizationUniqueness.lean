-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_polarizationUniqueness
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.polarizationUniqueness
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:46:52.701661+00:00
-- url     : https://prove2.me/theorems/998a5d59-74c7-4432-938d-3bbe503a895a
-- title:
--   Appendix B, Claim A 1: polarization uniqueness
-- statement:
--   Let $H$ be a complete real Hilbert space, possibly infinite-dimensional. Suppose $\beta:H\to\mathbb R$ is a bounded quadratic form, meaning $\beta(v)=B(v,v)$ for some bounded symmetric real bilinear form. There is a unique such form, and
--   $$B(v,w)=\tfrac12\bigl(\beta(v+w)-\beta(v)-\beta(w)\bigr)\qquad(v,w\in H).$$
--   No positivity of $\beta$ is required. This determines the bilinear form from its diagonal.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 35, Appendix B, Claim A 1: polarization uniqueness

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Appendix B, Claim A 1, PDF pp.35--36: uniqueness and polarization on
an arbitrary real Hilbert space, without positivity or finite dimension. -/
theorem polarizationUniqueness {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (beta : H → ℝ)
    (hbeta : IsBoundedQuadratic beta) :
    (∃! B : H →L[ℝ] H →L[ℝ] ℝ,
      (∀ v w, B v w = B w v) ∧ ∀ v, beta v = B v v) ∧
    ∀ B : H →L[ℝ] H →L[ℝ] ℝ, (∀ v w, B v w = B w v) →
      (∀ v, beta v = B v v) →
      ∀ v w, B v w = (beta (v + w) - beta v - beta w) / 2 := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
