-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_entropy_powerLog_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.entropy_powerLog_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:47:44.885019+00:00
-- url     : https://prove2.me/theorems/5476c637-e643-4336-bfe0-f94c25c3c6e3
-- title:
--   Lemma 6.2: power-log equivalence of entropy and small balls
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space with RKHS unit ball $H_1$. For $\alpha>0$ and $\beta\in\mathbb R$, as $\varepsilon\downarrow0$,
--   $$\varphi_0(\varepsilon)\asymp\varepsilon^{-\alpha}(\log(1/\varepsilon))^\beta
--   \iff
--   \log N(\varepsilon,H_1,\|\cdot\|)\asymp\varepsilon^{-2\alpha/(2+\alpha)}(\log(1/\varepsilon))^{2\beta/(2+\alpha)}.$$
--   Comparability uses positive constants before the radius. Restricting to sufficiently small radii below one makes all real powers well defined; the zero law makes both positive-rate comparisons false.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 17, Lemma 6.2: power-log equivalence of entropy and small balls

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

/-- Lemma 6.2: power-log equivalence of entropy and small balls, arXiv:0805.3252v1, PDF p.17.
No nonzero assumption is added to this iff. Thresholds can be reduced below one in AtZeroComparable. -/
theorem entropy_powerLog_equivalence
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) (a b : ℝ) (ha : 0 < a) :
    AtZeroComparable (smallBall P W) (powerLog a b) ↔
      AtZeroComparable (logCover (rkhsUnitBall P W))
        (powerLog (2 * a / (2 + a)) (2 * b / (2 + a))) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
