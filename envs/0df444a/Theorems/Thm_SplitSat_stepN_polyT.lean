-- Prove2me | Theorems.Thm_SplitSat_stepN_polyT
-- name    : SplitSat.stepN_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:49.837539+00:00
-- url     : https://prove2.me/theorems/e5d6a894-dca9-40c1-89be-34aa9ed97360
-- title:
--   Split Sat: step N poly T
-- statement:
--   The step of the tree with n carried along is polynomial time if the step of the tree is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L28-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L28-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Cert
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight.Width

theorem SplitSat.stepN_polyT {step : Fml → Option (Fml × Fml)} (hs : PolyT step) : PolyT (stepN step) := by sorry
