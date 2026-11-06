-- Prove2me | Theorems.Thm_P2M_hh__nonpos_f9599ae28637
-- name    : P2M_hh__nonpos_f9599ae28637
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:18:55.191661+00:00
-- url     : https://prove2.me/theorems/e8480348-9e76-42e4-8d48-68146b6b32c5
-- title:
--   P2 M hh  nonpos f9599ae28637: P2 M hh  nonpos f9599ae28637
-- statement:
--   The P2 M hh  nonpos f9599ae28637 construction uses the P2 M hh  nonpos f9599ae28637 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1051-L1054
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1051-L1054

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

theorem P2M_hh__nonpos_f9599ae28637 {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by sorry

alias «hh'_nonpos» := P2M_hh__nonpos_f9599ae28637
