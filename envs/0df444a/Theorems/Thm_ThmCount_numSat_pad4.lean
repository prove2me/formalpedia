-- Prove2me | Theorems.Thm_ThmCount_numSat_pad4
-- name    : ThmCount.numSat_pad4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:02.669931+00:00
-- url     : https://prove2.me/theorems/4188c0bd-84f7-485f-bcc2-b20da4f72ecf
-- title:
--   Thm Count: num Sat pad4
-- statement:
--   The four forced variables keep the number of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L104-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/FrontEnd.lean#L104-L124

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

theorem ThmCount.numSat_pad4 {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat (Wrap.pad4 φ) = SatK.numSat φ := by sorry
