-- Prove2me | Theorems.Thm_ThmCount_dropFour_binary
-- name    : ThmCount.dropFour_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:09:57.803976+00:00
-- url     : https://prove2.me/theorems/f48ec806-ce9f-4fb0-804c-12c00aa90eae
-- title:
--   Thm Count: drop Four binary
-- statement:
--   A number in n + 5 bits without its four highest bits is the number in n + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L127-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L127-L131

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

theorem ThmCount.dropFour_binary (n N : ℕ) : dropFour (SatK.binary (n + 4) N) = SatK.binary n N := by sorry
