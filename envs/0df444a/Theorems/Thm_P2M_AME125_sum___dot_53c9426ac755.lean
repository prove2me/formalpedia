-- Prove2me | Theorems.Thm_P2M_AME125_sum___dot_53c9426ac755
-- name    : P2M_AME125_sum___dot_53c9426ac755
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:22.729923+00:00
-- url     : https://prove2.me/theorems/5be3a2f8-88be-4c95-b37a-1748c3a798fe
-- title:
--   P2 M AME125 sum   dot 53c9426ac755: P2 M AME125 sum   dot 53c9426ac755
-- statement:
--   The character sum over many levels: `∑ z, χ(∑ k, z k · e k)` is `5^k` if `e = 0` and `0`
--   otherwise.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L74-L82
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L74-L82

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem P2M_AME125_sum___dot_53c9426ac755 {k : ℕ} (e : Fin k → ZMod 5) :
    ∑ z : Fin k → ZMod 5, χ (∑ j, z j * e j) = if e = 0 then (5 : ℂ) ^ k else 0 := by sorry

alias «AME125».«sum_χ_dot» := P2M_AME125_sum___dot_53c9426ac755
