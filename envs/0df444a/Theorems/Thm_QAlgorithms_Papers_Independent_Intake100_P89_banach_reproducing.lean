-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_banach_reproducing
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.banach_reproducing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:34:57.308355+00:00
-- url     : https://prove2.me/theorems/60a19e8b-de4b-4b4b-9d94-3b0400039621
-- title:
--   §2.2, Banach RKHS reproducing formula (2.6)
-- statement:
--   For a Borel centered Gaussian element $W$ in a real separable Banach space $B$, write $S\ell=E[W\ell(W)]$. Every $S\ell$ belongs to the covariance RKHS $H$, and
--   $$\langle S\ell,h\rangle_H=\ell(h)\quad(\ell\in B^*,\ h\in H).$$
--   This reproducing identity identifies dual evaluation with the Hilbert pairing; the B-valued covariance and its lift are related by the canonical embedding.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 5, §2.2, Banach RKHS reproducing formula (2.6)

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

/-- §2.2, Banach RKHS reproducing formula (2.6), arXiv:0805.3252v1, PDF p.5.
The first clause fixes the actual covariance lift; the displayed pairing has the source ordering. -/
theorem banach_reproducing
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (∀ l : B →L[ℝ] ℝ, covarianceMap P W l ∈ banachRKHS P W ∧
      banachLift P W (covarianceMap P W l) = analysisMap P W l) ∧
    ∀ (l : B →L[ℝ] ℝ) (h : B), h ∈ banachRKHS P W →
      banachInner P W (covarianceMap P W l) h = l h := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
