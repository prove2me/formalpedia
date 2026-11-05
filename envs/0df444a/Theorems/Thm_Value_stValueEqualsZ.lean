-- Prove2me | Theorems.Thm_Value_stValueEqualsZ
-- name    : Value.stValueEqualsZ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:54:45.146465+00:00
-- url     : https://prove2.me/theorems/484c8490-daab-462b-a30a-09f0733fdc1b
-- title:
--   Value: st Value Equals Z
-- statement:
--   **«… so the value equals Z»**: the clique of the groups, as the network of Definition 3, has the
--   value of the network N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L39-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

theorem Value.stValueEqualsZ : StValueEqualsZ := by sorry
