-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_rkhs_unitBall_precompact
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.rkhs_unitBall_precompact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:36:48.623773+00:00
-- url     : https://prove2.me/theorems/d534746a-3438-4ace-b02a-4e869b57976d
-- title:
--   §2.2, unnumbered precompactness consequence
-- statement:
--   For a Borel centered Gaussian random element $W$ in a real separable Banach space $B$, let $H_1$ denote the embedded closed unit ball of its RKHS. Then
--   $$\overline{H_1}^{\,B}\ \text{is compact}.$$
--   This is precompactness in the ambient norm; it makes no compactness assertion in the Hilbert norm. The source repeats the consequence on PDF p.17.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 6, §2.2, unnumbered precompactness consequence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section BanachResults

variable {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]

variable [hComplete : CompleteSpace B] [hSeparable : TopologicalSpace.SeparableSpace B]

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP hComplete hSeparable

/-- §2.2, unnumbered precompactness consequence, arXiv:0805.3252v1, PDF p.6.
Inventoried once, PDF pp.6 and 17; ambient closure and topology are explicit. -/
theorem rkhs_unitBall_precompact
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    IsCompact (closure (rkhsUnitBall P W)) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
