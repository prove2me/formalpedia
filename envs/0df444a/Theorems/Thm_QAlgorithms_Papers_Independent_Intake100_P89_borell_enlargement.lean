-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_borell_enlargement
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.borell_enlargement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:45:07.913222+00:00
-- url     : https://prove2.me/theorems/7bce727f-d526-4166-bad2-0f933a7acc6f
-- title:
--   Theorem 5.1: Borell enlargement inequality (survey formulation)
-- statement:
--   For a Borel centered Gaussian element $W$ of a real separable Banach space $B$, let $H_1$ and $B_1$ be its closed RKHS and ambient unit balls. For $\varepsilon>0$ and $M\ge0$, set $p=P(\|W\|\le\varepsilon)$. Then
--   $$P\{W\in\varepsilon B_1+MH_1\}\ge\Phi(\Phi^{-1}(p)+M).$$
--   The right side is interpreted as $1$ at $p=1$ and $0$ at $p=0$. This retains the zero-law endpoint and the full enlargement geometry.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 14, Theorem 5.1: Borell enlargement inequality (survey formulation)

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

/-- Theorem 5.1: Borell enlargement inequality (survey formulation), arXiv:0805.3252v1, PDF p.14.
Closed balls match the median argument; positive-radius open and closed Gaussian norm balls have the same mass. The p=1 endpoint is explicit. -/
theorem borell_enlargement
(W : Omega → B) (hW : BorelCenteredGaussianElement P W)
    (e m : ℝ) (he : 0 < e) (hm : 0 ≤ m) :
    (P {o | ∃ h ∈ rkhsUnitBall P W, ‖W o - m • h‖ ≤ e}).toReal ≥
      normalEnlargement ((P {o | ‖W o‖ ≤ e}).toReal) m := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
