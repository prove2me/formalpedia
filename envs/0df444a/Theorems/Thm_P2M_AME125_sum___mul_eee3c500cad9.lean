-- Prove2me | Theorems.Thm_P2M_AME125_sum___mul_eee3c500cad9
-- name    : P2M_AME125_sum___mul_eee3c500cad9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:10.465826+00:00
-- url     : https://prove2.me/theorems/9ddace5e-b1ea-47af-a88d-fcd1357f5cb1
-- title:
--   P2 M AME125 sum   mul eee3c500cad9: P2 M AME125 sum   mul eee3c500cad9
-- statement:
--   The character sum over one level: `∑ t, χ(t · e)` is `5` if `e = 0` and `0` otherwise.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L68-L70
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L68-L70

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem P2M_AME125_sum___mul_eee3c500cad9 (e : ZMod 5) : ∑ t : ZMod 5, χ (t * e) = if e = 0 then 5 else 0 := by sorry

alias «AME125».«sum_χ_mul» := P2M_AME125_sum___mul_eee3c500cad9
