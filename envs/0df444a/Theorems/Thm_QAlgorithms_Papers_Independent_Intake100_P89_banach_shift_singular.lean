-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_banach_shift_singular
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.banach_shift_singular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:40:24.826527+00:00
-- url     : https://prove2.me/theorems/c720e376-84de-4620-8e5d-7b00f6fbc100
-- title:
--   Lemma 3.3
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space $B$, with covariance RKHS $H$. For every fixed $b\in B\setminus H$,
--   $$P^{W+b}\perp P^W.$$
--   The conclusion holds even for shifts in the ambient closure of $H$. No separability assumption on the dual is imposed.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 9, Lemma 3.3

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

/-- Lemma 3.3, arXiv:0805.3252v1, PDF p.9.
The source proof wrongly requests a norm-dense countable dual family; the valid statement needs no such hypothesis. -/
theorem banach_shift_singular
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) (b : B)
    (hb : b ∉ banachRKHS P W) :
    (borelLaw P (fun o => W o + b)).MutuallySingular (borelLaw P W) := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
