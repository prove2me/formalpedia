-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_brownian_cameronMartin
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.brownian_cameronMartin
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:51:29.890247+00:00
-- url     : https://prove2.me/theorems/7378d0a7-89e5-490a-a28a-accf4fad4a55
-- title:
--   Lemma 10.1: Brownian Cameron–Martin space
-- statement:
--   Let $W$ be standard real Brownian motion on $[0,1]$, in its Borel continuous version. Its RKHS consists precisely of absolutely continuous functions $h$ with $h(0)=0$ and square-integrable a.e. derivative. Equivalently, $h(t)=\int_0^tg(s)\,ds$ for a unique $g\in L^2[0,1]$, and
--   $$\langle h_1,h_2\rangle_H=\int_0^1h_1'(s)h_2'(s)\,ds=\langle g_1,g_2\rangle_2.$$
--   The integral parametrization retains derivatives as equivalence classes and identifies the Banach and coordinate-process models.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 19, Lemma 10.1: Brownian Cameron–Martin space

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

/-- Lemma 10.1: Brownian Cameron–Martin space, arXiv:0805.3252v1, PDF p.19.
AC with L² derivative is encoded by its exact Lebesgue-primitive parametrization, not by pointwise derivatives. Initial zero is built into primitive. -/
theorem brownian_cameronMartin
(W : Omega → C(Time, ℝ)) (hW : StandardBrownian P W) :
    processRKHS P (fun t o => W o t) = Set.range (fun g : TimeL2 => primitive g) ∧
    Function.Injective (fun g : TimeL2 => primitive g) ∧
    (∀ f g : TimeL2,
      processInner P (fun t o => W o t) (primitive f) (primitive g) = inner ℝ f g) ∧
    (fun h : C(Time, ℝ) => fun t => h t) '' banachRKHS P W =
      Set.range (fun g : TimeL2 => primitive g) := by sorry

end PathResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
