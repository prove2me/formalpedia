-- Prove2me | Theorems.Thm_P2M_W21_hf__c0784783506d
-- name    : P2M_W21_hf__c0784783506d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:33:56.454826+00:00
-- url     : https://prove2.me/theorems/5f9c870d-7093-4f7a-aa05-3f6a3eb586bb
-- title:
--   P2 M W21 hf  c0784783506d: P2 M W21 hf  c0784783506d
-- statement:
--   The P2 M W21 hf  c0784783506d construction uses the P2 M W21 hf  c0784783506d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L238-L239
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L238-L239

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open W21
variable {f : W21}

theorem P2M_W21_hf__c0784783506d (f : W21) : Integrable (deriv f) := by sorry

alias «W21».«hf'» := P2M_W21_hf__c0784783506d
