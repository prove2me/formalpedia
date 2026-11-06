-- Prove2me | Theorems.Thm_SplitCount_stepPlain_polyT
-- name    : SplitCount.stepPlain_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:31.810953+00:00
-- url     : https://prove2.me/theorems/7646b2e0-31d7-49f1-bc5d-7ed5c1dfae89
-- title:
--   Split Count: step Plain poly T
-- statement:
--   The step of the tree with n handed down is polynomial-time if the step of the tree is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L31-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Cert.lean#L31-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_SplitCount_Cert
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat Eight.Width Occ

theorem SplitCount.stepPlain_polyT {step : CNode → Option (CNode × CNode)} (hs : PolyT step) : PolyT (stepPlain step) := by sorry
