-- Prove2me | Theorems.Thm_W21_approximation
-- name    : W21_approximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:17:15.89129+00:00
-- url     : https://prove2.me/theorems/d418e2a0-d762-473d-a6d6-ea4d01d38868
-- title:
--   W21 approximation: W21 approximation
-- statement:
--   The W21 approximation construction uses the W21 approximation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L246-L379
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L246-L379

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by sorry
