-- Prove2me | Theorems.Thm_W21_hf
-- name    : W21.hf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:33:37.059063+00:00
-- url     : https://prove2.me/theorems/cdc682ca-b3ab-42f5-9eec-d565cfb3e3cd
-- title:
--   W21: hf
-- statement:
--   The W21 construction uses the hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L236-L236
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L236-L236

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

theorem W21.hf (f : W21) : Integrable f := by sorry
