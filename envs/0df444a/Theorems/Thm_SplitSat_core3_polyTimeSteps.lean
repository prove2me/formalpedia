-- Prove2me | Theorems.Thm_SplitSat_core3_polyTimeSteps
-- name    : SplitSat.core3_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:36.637212+00:00
-- url     : https://prove2.me/theorems/3399ef8d-9afb-4d06-a3e1-40c8c463684f
-- title:
--   Split Sat: core3 poly Time Steps
-- statement:
--   The steps of `core3 ℓ τ` are polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L41-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L41-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic
import Definitions.Def_SplitSat_Procedure
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight Eight.ViaGrouping GraphProblems

theorem SplitSat.core3_polyTimeSteps (ℓ τ : ℕ) : PolyTimeSteps (core3 ℓ τ) := by sorry
