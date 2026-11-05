-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_eq_of_blocks
-- name    : PaddedDescent.F.Mark.Code.eq_of_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:50.524325+00:00
-- url     : https://prove2.me/theorems/3f9ccdb2-c171-4c59-bd27-981cab9cf680
-- title:
--   Code: eq of blocks
-- statement:
--   Several blocks are read back, whatever follows them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L74-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L74-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_flatMap
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.flatMap


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.eq_of_blocks {β b : ℕ} (hb : b ≤ 2 ^ β) {x x' : List Bool} : ∀ (os : List ℕ) {r r' : List Bool},
    os.flatMap (blkc β b x) ++ r = os.flatMap (blkc β b x') ++ r' → (∀ o ∈ os, ones b x o = ones b x' o) ∧ r = r'
  := by sorry
