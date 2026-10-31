-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_entropy_smallBall_comparisons
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.entropy_smallBall_comparisons
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:47:19.472661+00:00
-- url     : https://prove2.me/theorems/aa0a6b21-10cc-43bd-8342-7b7debfd5dbc
-- title:
--   Lemma 6.1: four entropy/small-ball comparisons
-- statement:
--   Let $W$ be a nonzero Borel centered Gaussian element of a real separable Banach space, $H_1$ its embedded RKHS unit ball, $L(r)=\log N(r,H_1,\|\cdot\|)$, and $\varphi_0(r)=-\log P(\|W\|<r)$. For any measurable positive function $f$ regularly varying at zero, all comparisons as $\varepsilon\downarrow0$ hold:
--   $$\begin{aligned}L(\varepsilon/\sqrt{2\varphi_0(\varepsilon)})&\gtrsim\varphi_0(2\varepsilon),\\
--   \varphi_0\lesssim f&\implies L(\varepsilon/\sqrt{f(\varepsilon)})\lesssim f(\varepsilon),\\
--   L\gtrsim f&\implies\varphi_0(\varepsilon)\gtrsim f(\varepsilon/\sqrt{\varphi_0(\varepsilon)}),\\
--   L\lesssim f&\implies\varphi_0(2\varepsilon)\lesssim f(\varepsilon/\sqrt{\varphi_0(\varepsilon)}).\end{aligned}$$
--   Every comparison constant is independent of sufficiently small positive radii. Nonzero excludes the undefined zero-law rescalings.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 17, Lemma 6.1: four entropy/small-ball comparisons

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

/-- Lemma 6.1: four entropy/small-ball comparisons, arXiv:0805.3252v1, PDF p.17.
SOURCE CORRECTION: printed f(e) in (ii) is f(epsilon), fixed by surrounding formulas. The nonzero hypothesis makes explicit the implicit positive small-ball-exponent domain. PDF p.17 rendered and checked; independent moderation required. -/
theorem entropy_smallBall_comparisons
(W : Omega → B) (hW : BorelCenteredGaussianElement P W)
    (hnonzero : ¬ (∀ᵐ o ∂P, W o = 0)) (f : ℝ → ℝ) (hf : RegularAtZero f) :
    (∀ e : ℝ, 0 < e → ∃ n, HasCover (rkhsUnitBall P W) e n) ∧
    AtZeroLE (fun e => smallBall P W (2 * e))
      (fun e => logCover (rkhsUnitBall P W) (e / Real.sqrt (2 * smallBall P W e))) ∧
    (AtZeroLE (smallBall P W) f →
      AtZeroLE (fun e => logCover (rkhsUnitBall P W) (e / Real.sqrt (f e))) f) ∧
    (AtZeroLE f (logCover (rkhsUnitBall P W)) →
      AtZeroLE (fun e => f (e / Real.sqrt (smallBall P W e))) (smallBall P W)) ∧
    (AtZeroLE (logCover (rkhsUnitBall P W)) f →
      AtZeroLE (fun e => smallBall P W (2 * e))
        (fun e => f (e / Real.sqrt (smallBall P W e)))) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
