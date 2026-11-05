-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_fold_total
-- name    : QueryMachines.Bridge.Proof.fold_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:24:04.069013+00:00
-- url     : https://prove2.me/theorems/e37b9252-d4f2-470a-9cd0-df1be2d50585
-- title:
--   Proof: fold total
-- statement:
--   So do any number of rounds keep that sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L145-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Compare.lean#L145-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_CountedToPadded_Compare
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Turing Groundwork Groundwork.TM Groundwork.PolyT

theorem QueryMachines.Bridge.Proof.fold_total (l : List Unit) : ∀ s : List V × ℕ, (l.foldl (fun s _ => visit s) s).2 + total (l.foldl (fun s _ => visit s) s).1 = s.2 + total s.1 := by sorry
