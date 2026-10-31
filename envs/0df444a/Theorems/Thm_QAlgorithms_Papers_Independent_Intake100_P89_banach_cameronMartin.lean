-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_banach_cameronMartin
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.banach_cameronMartin
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:39:58.374583+00:00
-- url     : https://prove2.me/theorems/0161faf0-2281-4587-a01d-a76c3fcab880
-- title:
--   Lemma 3.2
-- statement:
--   Let $W$ be a Borel centered Gaussian element in a real separable Banach space, and let $h$ belong to its covariance RKHS. On the Borel sigma algebra, the laws of $W+h$ and $W$ are mutually absolutely continuous, with
--   $$\frac{dP^{W+h}}{dP^W}(W)=\exp\{Uh-\tfrac12\|h\|_H^2\}\quad P\text{-a.s.}$$
--   Here $U(S\ell)=\ell(W)$ and $U$ is extended continuously to the RKHS.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 9, Lemma 3.2

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

/-- Lemma 3.2, arXiv:0805.3252v1, PDF p.9.
The positive sign of U h and both absolute-continuity directions are retained. -/
theorem banach_cameronMartin
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) (h : B)
    (hh : h ∈ banachRKHS P W) :
    borelLaw P (fun o => W o + h) ≪ borelLaw P W ∧
    borelLaw P W ≪ borelLaw P (fun o => W o + h) ∧
    ∀ᵐ o ∂P,
      ((borelLaw P (fun o => W o + h)).rnDeriv (borelLaw P W) (W o)).toReal =
        Real.exp ((banachLift P W h) o - banachNorm P W h ^ 2 / 2) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
