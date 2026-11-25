-- Prove2me | Theorems.Thm_ShannonCapacity_shannonCapacity_cycle_five
-- name    : ShannonCapacity.shannonCapacity_cycle_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:08:03.804402+00:00
-- url     : https://prove2.me/theorems/62cfe63a-c451-494e-afc1-a89282cfbfbe
-- title:
--   Shannon Capacity: shannon Capacity cycle five
-- statement:
--   **Lovász (1979).** The Shannon capacity of the pentagon is `√5`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L73-L74
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L73-L74

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_shannonCapacity_cycle_five

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}

theorem ShannonCapacity.shannonCapacity_cycle_five : shannonCapacity (cycleGraph 5) = Real.sqrt 5 := by sorry
