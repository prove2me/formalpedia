-- Prove2me | Theorems.Thm_P2M_WI_sum_Iab_le__d930876d6e3b
-- name    : P2M_WI_sum_Iab_le__d930876d6e3b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:21:14.063708+00:00
-- url     : https://prove2.me/theorems/71c21274-cd58-488a-965b-68359b7c7b88
-- title:
--   P2 M WI sum Iab le  d930876d6e3b: P2 M WI sum Iab le  d930876d6e3b
-- statement:
--   The P2 M WI sum Iab le  d930876d6e3b construction uses the P2 M WI sum Iab le  d930876d6e3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1814-L1818
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L1814-L1818

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
attribute [local instance] _p2m_local_instance_2ee1fa6ce2_1687

theorem P2M_WI_sum_Iab_le__d930876d6e3b {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ}
    (hcheby : (∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n))
    (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by sorry

alias «WI_sum_Iab_le'» := P2M_WI_sum_Iab_le__d930876d6e3b
