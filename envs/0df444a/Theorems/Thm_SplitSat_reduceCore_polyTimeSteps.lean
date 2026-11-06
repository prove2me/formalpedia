-- Prove2me | Theorems.Thm_SplitSat_reduceCore_polyTimeSteps
-- name    : SplitSat.reduceCore_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:29:10.966873+00:00
-- url     : https://prove2.me/theorems/d1801b67-1b2b-4ab3-a6bf-90f190bf6698
-- title:
--   Split Sat: reduce Core poly Time Steps
-- statement:
--   The steps of the reduction without its reader are polynomial time, if the step of the tree is
--   polynomial time and the steps of D are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L34-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Cert.lean#L34-L43

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

theorem SplitSat.reduceCore_polyTimeSteps {step : Fml → Option (Fml × Fml)} (hs : PolyT step) {D : StepMachine (List Unit × Fml) Bool} (hD : PolyTimeSteps D) :
    PolyTimeSteps (reduceCore step D) := by sorry
