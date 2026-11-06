-- Prove2me | Theorems.Thm_Printed_threeSat_by_algorithm
-- name    : Printed.threeSat_by_algorithm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:04:37.07523+00:00
-- url     : https://prove2.me/theorems/d4b91d0a-09ec-42a5-9045-a9ecaa9de552
-- title:
--   Printed: three Sat by algorithm
-- statement:
--   **Theorem 2 in its decision form**, by Algorithm 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/End.lean#L112-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/End.lean#L112-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Proof
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Grouping
import Definitions.Def_Variance_Grouping
import Definitions.Def_Exits_End
import Definitions.Def_Value_End
import Definitions.Def_Suffices_Main
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Printed_End
import Theorems.Thm_Exits_threeSat_by_algorithm

set_option autoImplicit false
section
section
open Printed

theorem Printed.threeSat_by_algorithm : Sat3.ThmEveryDelta := by sorry
