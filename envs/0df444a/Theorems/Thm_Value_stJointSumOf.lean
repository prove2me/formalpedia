-- Prove2me | Theorems.Thm_Value_stJointSumOf
-- name    : Value.stJointSumOf
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:26:24.510278+00:00
-- url     : https://prove2.me/theorems/34802da1-7bb1-4db8-8b2b-03f42448f943
-- title:
--   Value: st Joint Sum Of
-- statement:
--   «Together with the sums inside the tables, this is a sum over all z ∈ ∏_{a ∈ [g]} S_a and over
--   one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups», from the
--   sentences before it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L85-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L85-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}

theorem Value.stJointSumOf : StJointSumOf := by sorry
