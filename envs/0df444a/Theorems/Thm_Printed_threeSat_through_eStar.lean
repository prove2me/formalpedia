-- Prove2me | Theorems.Thm_Printed_threeSat_through_eStar
-- name    : Printed.threeSat_through_eStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:48:25.222193+00:00
-- url     : https://prove2.me/theorems/0a552e27-bad1-44ff-b740-8524951bc0bf
-- title:
--   Printed: three Sat through e Star
-- statement:
--   **Theorem 2 in its decision form**, by the proof of Section 6: through e* = 0 for the printed
--   Definition 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/End.lean#L109-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/End.lean#L109-L109

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
import Theorems.Thm_Exits_threeSat_through_eStar

set_option autoImplicit false
section
section
open Printed

theorem Printed.threeSat_through_eStar : Sat3.ThmEveryDelta := by sorry
