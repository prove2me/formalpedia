-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_bounded_stieltjes_inclusions
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.bounded_stieltjes_inclusions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:10:10.908694+00:00
-- url     : https://prove2.me/theorems/084437f3-e81d-489c-b6ff-45765be8ec70
-- title:
--   Nesting and multiplication of bounded Stieltjes classes
-- statement:
--   Let $S_\alpha$ be the generalised Stieltjes class with nonnegative constant term and positive Radon representing measure satisfying the weighted integrability condition. Let $S_{\alpha,b}$ consist of its members represented by $f(z)=\int_{[0,\infty)}(1+zs)^{-\alpha}\,\nu(ds)$ for a finite positive measure $\nu$. Then
--
--   $$S_{\alpha,b}\subseteq S_{\beta,b}\quad(0<\alpha<\beta),\qquad S_{\alpha,b}S_{\beta,b}\subseteq S_{\alpha+\beta,b}\quad(\alpha,\beta>0).$$
--
--   All functions have the common domain $(0,\infty)$, and products are pointwise. Both inclusions enter the construction of the bounded algebra.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 13, Proposition 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]

variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Proposition 4.2, PDF p.13: both bounded-class inclusions, with positive orders. -/
theorem bounded_stieltjes_inclusions :
    (∀ alpha beta : ℝ, 0 < alpha → alpha < beta →
      BoundedStieltjesClass alpha ⊆ BoundedStieltjesClass beta) ∧
    (∀ alpha beta : ℝ, 0 < alpha → 0 < beta →
      ∀ f ∈ BoundedStieltjesClass alpha, ∀ g ∈ BoundedStieltjesClass beta,
        (fun z => f z * g z) ∈ BoundedStieltjesClass (alpha + beta)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
