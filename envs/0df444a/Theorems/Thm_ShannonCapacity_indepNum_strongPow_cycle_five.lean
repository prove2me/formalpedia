-- Prove2me | Theorems.Thm_ShannonCapacity_indepNum_strongPow_cycle_five
-- name    : ShannonCapacity.indepNum_strongPow_cycle_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:51:05.388043+00:00
-- url     : https://prove2.me/theorems/501e1a92-db43-4751-8942-127d1e04f6e3
-- title:
--   Shannon Capacity: indep Num strong Pow cycle five
-- statement:
--   For the 5-cycle, `α(C₅^⊠k)² ≤ 5^k`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L60-L62
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L60-L62

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_cycle_five

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}

theorem ShannonCapacity.indepNum_strongPow_cycle_five (k : ℕ) :
    (strongPow (cycleGraph 5) k).indepNum ^ 2 ≤ 5 ^ k := by sorry
