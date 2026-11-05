-- Prove2me | Theorems.Thm_WidthK_Refine_exists_mask
-- name    : WidthK.Refine.exists_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:34.379317+00:00
-- url     : https://prove2.me/theorems/e59100fc-bdc5-48f7-b98f-7415a1d56c9a
-- title:
--   Refine: exists mask
-- statement:
--   Every sublist of a clause of at most k literals is picked by one of the masks of length k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L129-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L129-L149

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.exists_mask {k : ℕ} {C H : PCl} (hC : C.length ≤ k) (hH : H.Sublist C) : ∃ m ∈ masks k, maskP m C = H := by sorry
