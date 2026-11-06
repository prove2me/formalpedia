-- Prove2me | Theorems.Thm_SplitSat_final_bound
-- name    : SplitSat.final_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:57.213206+00:00
-- url     : https://prove2.me/theorems/773bb634-a2f8-494e-be1f-20805ad64a5b
-- title:
--   Split Sat: final bound
-- statement:
--   The sizes that occur in the proof of `reduceCore_decides` are at most c'·W^c', where W = n + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L167-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L167-L181

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_Prog_SatTopK_final_bound

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.final_bound (P₂ P₀ R c e W : ℕ) (h1 : 1 ≤ W) :
    P₂ * W ^ e + c * (R * W) ^ c + 4 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e ∧ P₀ * W ^ e + 3 ≤ cOf P₂ P₀ R c e * W ^ cOf P₂ P₀ R c e := by sorry
