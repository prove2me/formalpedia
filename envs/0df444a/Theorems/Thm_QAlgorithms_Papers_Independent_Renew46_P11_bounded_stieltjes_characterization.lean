-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P11_bounded_stieltjes_characterization
-- name    : QAlgorithms.Papers.Independent.Renew46.P11.bounded_stieltjes_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:12:58.482986+00:00
-- url     : https://prove2.me/theorems/f8fe69d1-56da-4d15-9718-039f002c26c1
-- title:
--   Bounded Stieltjes functions and the mass formula
-- statement:
--   Let $\alpha>0$ and $f\in S_\alpha$, with $S_\alpha$ defined by the positive Radon measure representation including a nonnegative constant and the weighted integrability condition. Let $S_{\alpha,b}$ denote the finite-measure representation class. Then $f\in S_{\alpha,b}$ if and only if $f$ is bounded above on $(0,\infty)$. For every finite positive measure $\nu$ representing $f(z)=\int_{[0,\infty)}(1+zs)^{-\alpha}\,\nu(ds)$,
--
--   $$\sup_{z>0} f(z)=\lim_{z\downarrow0}f(z)=\nu([0,\infty)).$$
--
--   The supremum is a real supremum of a bounded nonempty set. Atoms at zero, including constant functions, are retained in this quantitative characterisation.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, PDF p. 13, Unnumbered boundedness characterization in Section 4.1

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

/-- Section 4.1 boundedness characterisation, PDF pp.12–13.
The supremum is used only for bounded nonempty ranges, and the measure is
an actual representing measure. The limit is through positive arguments. -/
theorem bounded_stieltjes_characterization (alpha : ℝ) (ha : 0 < alpha)
    (f : PositiveReal → ℝ) (hf : f ∈ StieltjesClass alpha) :
    (f ∈ BoundedStieltjesClass alpha ↔ BddAbove (Set.range f)) ∧
    (∀ nu : Measure ℝ≥0, BoundedStieltjesRepresentation alpha f nu →
      sSup (Set.range f) = (nu Set.univ).toReal ∧
      Tendsto f (Filter.comap (fun z : PositiveReal => z.1) (𝓝[>] (0 : ℝ)))
        (𝓝 ((nu Set.univ).toReal))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P11

end
