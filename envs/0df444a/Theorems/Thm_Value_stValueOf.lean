-- Prove2me | Theorems.Thm_Value_stValueOf
-- name    : Value.stValueOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:25:25.288934+00:00
-- url     : https://prove2.me/theorems/fb69aeff-0c56-4828-a328-6f6e1ed5a82c
-- title:
--   Value: st Value Of
-- statement:
--   From «so the value equals Z» for the clique as a network to the form with one string per edge
--   and the tables `Paper.groupedTables`: back by the sentence after Definition 3, and the tables are
--   given by the display of W̃_γ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L44-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/End.lean#L44-L50

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

theorem Value.stValueOf : StValueOf := by sorry
