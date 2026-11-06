-- Prove2me | Theorems.Thm_ThmCount_encPlain_polyT
-- name    : ThmCount.encPlain_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:15.675492+00:00
-- url     : https://prove2.me/theorems/c957b3e3-d351-49b8-85e6-bb532b185025
-- title:
--   Thm Count: enc Plain poly T
-- statement:
--   Writing the code is polynomial time, with the number of variables and the number of bits of a
--   slot in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L65-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L65-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode

theorem ThmCount.encPlain_polyT {α : Type} [Enc α] {u w : α → List Unit} {F : α → NCNF} (hu : PolyT u) (hw : PolyT w) (hF : PolyT F) :
    PolyT fun x => encPlain (u x) (w x) (F x) := by sorry
