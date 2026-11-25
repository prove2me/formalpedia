-- Prove2me | Theorems.Thm_ShannonCapacity_indepNum_strongPow_cycle_five_two
-- name    : ShannonCapacity.indepNum_strongPow_cycle_five_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:59:09.850025+00:00
-- url     : https://prove2.me/theorems/9fb57286-8624-488f-b3cf-74fc7986a8e5
-- title:
--   Shannon Capacity: indep Num strong Pow cycle five two
-- statement:
--   **Shannon (1956).** `α(C₅^⊠2) = 5`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L65-L66
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L65-L66

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five_two

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}

theorem ShannonCapacity.indepNum_strongPow_cycle_five_two : (strongPow (cycleGraph 5) 2).indepNum = 5 := by sorry
