-- Prove2me | Theorems.Thm_ThmCount_stInputLength
-- name    : ThmCount.stInputLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:09:38.886314+00:00
-- url     : https://prove2.me/theorems/8002b2b4-a006-4eea-963f-25e9b7b2ad58
-- title:
--   Thm Count: st Input Length
-- statement:
--   The plain code of a 3-CNF on n variables has length at most 25·(n+2)^4: the statement
--   `ThmCount.StInputLength`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L141-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L141-L141

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

theorem ThmCount.stInputLength : StInputLength := by sorry
