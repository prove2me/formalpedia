-- Prove2me | Theorems.Thm_Value_stCliqueValue
-- name    : Value.stCliqueValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:35:35.56906+00:00
-- url     : https://prove2.me/theorems/e568a6a3-2e62-4efd-bcbd-7685b65e323f
-- title:
--   Value: st Clique Value
-- statement:
--   The remark after Definition 3: the value of the clique is the sum, over one string in {0,1}^λ
--   per edge, of ∏_{w∈[K]} W_w at the strings on the edges at w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L117-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L117-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks

theorem Value.stCliqueValue : StCliqueValue := by sorry
