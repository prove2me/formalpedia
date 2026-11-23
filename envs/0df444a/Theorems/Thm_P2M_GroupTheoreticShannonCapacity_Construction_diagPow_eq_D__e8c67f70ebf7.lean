-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
-- name    : P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:27:09.592073+00:00
-- url     : https://prove2.me/theorems/29916025-5577-49a8-97dc-62edaffc4548
-- title:
--   P2 M Group Theoretic Shannon Capacity Construction diag Pow eq D  e8c67f70ebf7: P2 M Group Theoretic Shannon Capacity Construction diag Pow eq D  e8c67f70ebf7
-- statement:
--   diagPow equals Dα
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1040-L1041
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1040-L1041

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7 (n : ℕ) (β : ℝ) : diagPow n β = MAlpha.Dα n β := by sorry

alias «GroupTheoreticShannonCapacity».«Construction».«diagPow_eq_Dα» := P2M_GroupTheoreticShannonCapacity_Construction_diagPow_eq_D__e8c67f70ebf7
