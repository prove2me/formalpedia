-- Prove2me | Theorems.Thm_P2M_pp__deriv_0c521294d559
-- name    : P2M_pp__deriv_0c521294d559
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:18:51.373693+00:00
-- url     : https://prove2.me/theorems/8e95e21f-d9b2-4b9a-833e-a7dfb51be2c8
-- title:
--   P2 M pp  deriv 0c521294d559: P2 M pp  deriv 0c521294d559
-- statement:
--   The P2 M pp  deriv 0c521294d559 construction uses the P2 M pp  deriv 0c521294d559 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1005-L1008
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1005-L1008

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem P2M_pp__deriv_0c521294d559 (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by sorry

alias «pp'_deriv» := P2M_pp__deriv_0c521294d559
