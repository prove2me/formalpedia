-- Prove2me | Theorems.Thm_SplitSat_core3_decides
-- name    : SplitSat.core3_decides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:35.290642+00:00
-- url     : https://prove2.me/theorems/b2ec7f4c-101c-4cb9-817e-f0605074ed61
-- title:
--   Split Sat: core3 decides
-- statement:
--   If `SATCp ℓ τ` decides 3-SAT on codes within c·2^{δn} steps, then `core3 ℓ τ` decides 3-SAT on
--   pairs (N in unary, formula) with the exponent δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L52-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L52-L73

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

theorem SplitSat.core3_decides {ℓ τ : ℕ} {δ : ℝ} (h : Paper.DecidesInSteps (ThreeSatPrinted.SATCp ℓ τ) δ) : ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c := by sorry
