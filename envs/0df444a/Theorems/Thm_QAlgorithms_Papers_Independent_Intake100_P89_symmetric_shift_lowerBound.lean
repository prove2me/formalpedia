-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_symmetric_shift_lowerBound
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.symmetric_shift_lowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:46:32.456609+00:00
-- url     : https://prove2.me/theorems/fe77247c-57bf-437a-9453-f0c3aa4b396c
-- title:
--   Lemma 5.2: lower bound for symmetric shifted sets
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space with RKHS $H$. For every $h\in H$ and every symmetric Borel set $C=-C$,
--   $$P(W-h\in C)\ge\exp(-\|h\|_H^2/2)\,P(W\in C).$$
--   The set need not be convex or a norm ball.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 15, Lemma 5.2: lower bound for symmetric shifted sets

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

/-- Lemma 5.2: lower bound for symmetric shifted sets, arXiv:0805.3252v1, PDF p.15.
Retains arbitrary symmetric Borel sets and the coefficient 1/2. -/
theorem symmetric_shift_lowerBound
(W : Omega → B) (hW : BorelCenteredGaussianElement P W) (h : B)
    (hh : h ∈ banachRKHS P W) (C : Set B)
    (hC : @MeasurableSet B (borel B) C) (hsymmetric : ∀ b : B, b ∈ C ↔ -b ∈ C) :
    (P {o | W o - h ∈ C}).toReal ≥
      Real.exp (-(banachNorm P W h) ^ 2 / 2) * (P {o | W o ∈ C}).toReal := by sorry

end BanachResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
