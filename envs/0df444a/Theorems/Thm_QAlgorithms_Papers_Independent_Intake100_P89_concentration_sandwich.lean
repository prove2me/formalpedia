-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_concentration_sandwich
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.concentration_sandwich
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:46:55.856378+00:00
-- url     : https://prove2.me/theorems/47f1c726-5fba-4c96-aa16-37abbf798333
-- title:
--   Lemma 5.3: concentration-function sandwich
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space with RKHS $H$. For $w$ in its support and $\varepsilon>0$, define
--   $$\varphi_w(\varepsilon)=\inf_{h\in H:\|h-w\|\le\varepsilon}\tfrac12\|h\|_H^2-\log P(\|W\|<\varepsilon).$$
--   Then
--   $$\varphi_w(\varepsilon)\le-\log P(\|W-w\|<\varepsilon)\le\varphi_w(\varepsilon/2).$$
--   The feasible sets are nonempty and bounded below, and both small-ball probabilities are positive. This compares shifted mass with approximation in the RKHS.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 16, Lemma 5.3: concentration-function sandwich

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

/-- Lemma 5.3: concentration-function sandwich, arXiv:0805.3252v1, PDF p.16.
The approximation constraint is closed; the probability balls are open. Explicit domain conclusions protect sInf and log from default values. -/
theorem concentration_sandwich
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) (w : B)
    (hw : w ∈ supportSet P W) (e : ℝ) (he : 0 < e) :
    (∀ r : ℝ, 0 < r →
      (∃ h ∈ banachRKHS P W, ‖h - w‖ ≤ r) ∧
      BddBelow {q : ℝ | ∃ h ∈ banachRKHS P W, ‖h - w‖ ≤ r ∧
        q = (banachNorm P W h) ^ 2 / 2}) ∧
    0 < P {o | ‖W o‖ < e} ∧ 0 < P {o | ‖W o - w‖ < e} ∧
    rkhsConcentration P W w e ≤ -Real.log ((P {o | ‖W o - w‖ < e}).toReal) ∧
    -Real.log ((P {o | ‖W o - w‖ < e}).toReal) ≤ rkhsConcentration P W w (e / 2) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
