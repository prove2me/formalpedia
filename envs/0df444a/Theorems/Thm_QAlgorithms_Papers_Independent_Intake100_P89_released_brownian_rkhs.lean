-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_released_brownian_rkhs
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.released_brownian_rkhs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:51:55.544094+00:00
-- url     : https://prove2.me/theorems/a26c0055-4e8d-41f0-820f-f6505b7d4c04
-- title:
--   §10, unnumbered Brownian motion started at a standard normal
-- statement:
--   Let $W$ be a continuous standard Brownian motion and $Z\sim N(0,1)$ independent of $W$. For $X_t=Z+W_t$, the RKHS consists of all absolutely continuous $h$ with square-integrable derivative, with no initial-value restriction:
--   $$\langle h,g\rangle_H=h(0)g(0)+\int_0^1h'(s)g'(s)\,ds.$$
--   Equivalently $h(t)=a+\int_0^tf$ with $(a,f)\in\mathbb R\times L^2[0,1]$.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 20, §10, unnumbered Brownian motion started at a standard normal

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section PathResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- §10, unnumbered Brownian motion started at a standard normal, arXiv:0805.3252v1, PDF p.20.
SOURCE CORRECTION: printed all absolutely continuous functions is read with L² derivative, explicitly required in the same paragraph. Without it the displayed Hilbert inner product need not be finite. -/
theorem released_brownian_rkhs
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W)
    (Z : Omega → ℝ) (hZ : Measurable Z) (hZlaw : P.map Z = gaussianReal 0 1)
    (hind : Indep (MeasurableSpace.comap Z inferInstance)
      (MeasurableSpace.comap W (borel C(Time, ℝ))) P) :
    let X := fun t : Time => fun o => Z o + W o t
    processRKHS P X = {h | ∃ a : ℝ, ∃ f : TimeL2, h = fun t => a + primitive f t} ∧
    ∀ (a b : ℝ) (f g : TimeL2),
      processInner P X (fun t => a + primitive f t) (fun t => b + primitive g t) =
        a * b + inner ℝ f g := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
