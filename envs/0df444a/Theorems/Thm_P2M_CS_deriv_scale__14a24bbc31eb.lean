-- Prove2me | Theorems.Thm_P2M_CS_deriv_scale__14a24bbc31eb
-- name    : P2M_CS_deriv_scale__14a24bbc31eb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:19.210527+00:00
-- url     : https://prove2.me/theorems/af57f9a5-e5de-44df-b168-c31e1a29c8f4
-- title:
--   P2 M CS deriv scale  14a24bbc31eb: P2 M CS deriv scale  14a24bbc31eb
-- statement:
--   The P2 M CS deriv scale  14a24bbc31eb construction uses the P2 M CS deriv scale  14a24bbc31eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L108-L111
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L108-L111

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}

theorem P2M_CS_deriv_scale__14a24bbc31eb {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by sorry

alias «CS».«deriv_scale'» := P2M_CS_deriv_scale__14a24bbc31eb
