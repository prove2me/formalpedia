-- Prove2me | Theorems.Thm_P2M_Finset_sum_shift_back__2bdb7b674e48
-- name    : P2M_Finset_sum_shift_back__2bdb7b674e48
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:47:41.021694+00:00
-- url     : https://prove2.me/theorems/93078f5f-9ac7-467a-81d9-ad0e8d0cea9f
-- title:
--   P2 M Finset sum shift back  2bdb7b674e48: P2 M Finset sum shift back  2bdb7b674e48
-- statement:
--   The P2 M Finset sum shift back  2bdb7b674e48 construction uses the P2 M Finset sum shift back  2bdb7b674e48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L399-L401
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L399-L401

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

theorem P2M_Finset_sum_shift_back__2bdb7b674e48 {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by sorry

alias «Finset».«sum_shift_back'» := P2M_Finset_sum_shift_back__2bdb7b674e48
