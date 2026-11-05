-- Prove2me | Theorems.Thm_WidthK_Refine_maskP_cons_true
-- name    : WidthK.Refine.maskP_cons_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:48.917082+00:00
-- url     : https://prove2.me/theorems/e0988052-7f3d-447d-b1fc-bdd481a80a81
-- title:
--   Refine: mask P cons true
-- statement:
--   The Refine construction uses the mask P cons true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L111-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L111-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.maskP_cons_true (m : List Bool) (a : PLit) (C : PCl) : maskP (true :: m) (a :: C) = a :: maskP m C := by sorry
