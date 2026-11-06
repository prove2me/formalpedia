-- Prove2me | Theorems.Thm_SplitSat_stCore3
-- name    : SplitSat.stCore3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:50:34.577646+00:00
-- url     : https://prove2.me/theorems/21f75ca4-c8a4-40e2-8d3c-630838422fcf
-- title:
--   Split Sat: st Core3
-- statement:
--   **«Theorem 2 gives s_3 = 0»**, for the machine of Theorem 2 in its decision form without its
--   reader: for every δ > 0 there are ℓ and τ such that `core3 ℓ τ` has polynomial-time steps and
--   decides 3-SAT with the exponent δ. This is the statement `SplitSat.StCore3`; ℓ and τ are those of
--   `ThreeSatPrinted.algPseudocode_decides_viaC`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L79-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L79-L81

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

theorem SplitSat.stCore3 : StCore3 := by sorry
