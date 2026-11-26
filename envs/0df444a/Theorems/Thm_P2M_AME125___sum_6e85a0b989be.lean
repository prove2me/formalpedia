-- Prove2me | Theorems.Thm_P2M_AME125___sum_6e85a0b989be
-- name    : P2M_AME125___sum_6e85a0b989be
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:11.73327+00:00
-- url     : https://prove2.me/theorems/0338e2c6-d016-41f3-805c-4528f1eb9408
-- title:
--   P2 M AME125   sum 6e85a0b989be: P2 M AME125   sum 6e85a0b989be
-- statement:
--   A character of a sum is the product of the characters.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L61-L65
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L61-L65

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem P2M_AME125___sum_6e85a0b989be {ι : Type*} (s : Finset ι) (f : ι → ZMod 5) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by sorry

alias «AME125».«χ_sum» := P2M_AME125___sum_6e85a0b989be
