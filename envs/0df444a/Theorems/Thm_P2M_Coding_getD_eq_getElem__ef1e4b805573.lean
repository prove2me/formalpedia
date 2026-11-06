-- Prove2me | Theorems.Thm_P2M_Coding_getD_eq_getElem__ef1e4b805573
-- name    : P2M_Coding_getD_eq_getElem__ef1e4b805573
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:44.012949+00:00
-- url     : https://prove2.me/theorems/7554eac8-764f-4fb9-ae8f-8120f0908d4a
-- title:
--   P2 M Coding get D eq get Elem  ef1e4b805573: P2 M Coding get D eq get Elem  ef1e4b805573
-- statement:
--   Inside the list, getD reads the entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L98-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccTests.lean#L98-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccMore
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccTests
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight
variable {Φ : Fml}

theorem P2M_Coding_getD_eq_getElem__ef1e4b805573 {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d = l[i] := by sorry

alias «Coding».«getD_eq_getElem'» := P2M_Coding_getD_eq_getElem__ef1e4b805573
