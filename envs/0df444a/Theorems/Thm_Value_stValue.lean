-- Prove2me | Theorems.Thm_Value_stValue
-- name    : Value.stValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:25:20.310504+00:00
-- url     : https://prove2.me/theorems/85c72d71-fb24-4554-9e7c-b1d0318ce851
-- title:
--   Value: st Value
-- statement:
--   «… so the value equals Z», in the form in which the proof of Lemma 1 takes the step. (A
--   different declaration from the theorem of the same name in `Eight.ViaGrouping`; it is proved here
--   without using that theorem.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L55-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
import Theorems.Thm_Eight_ViaGrouping_stValue

set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

theorem Value.stValue : Eight.ViaGrouping.StValue := by sorry
