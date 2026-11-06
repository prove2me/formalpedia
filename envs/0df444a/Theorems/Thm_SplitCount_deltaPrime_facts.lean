-- Prove2me | Theorems.Thm_SplitCount_deltaPrime_facts
-- name    : SplitCount.deltaPrime_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:45.2081+00:00
-- url     : https://prove2.me/theorems/5d235c0c-6dbd-45b0-a554-ed0cb2ae773f
-- title:
--   Split Count: delta Prime facts
-- statement:
--   «then δ' small enough»: for δ > 0 and w ≥ 3, δ' = `deltaPrime δ w Bl` is positive, at most 1,
--   and δ'·(1 + 3(w − 3))·(Bl + 1) ≤ δ/3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Main.lean#L43-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Main.lean#L43-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SplitCount_Main
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem SplitCount.deltaPrime_facts {δ : ℝ} (hδ : 0 < δ) {w : ℕ} (hw : 3 ≤ w) (Bl : ℕ) :
    0 < deltaPrime δ w Bl ∧ deltaPrime δ w Bl ≤ 1 ∧ deltaPrime δ w Bl * ((1 + 3 * ((w : ℝ) - 3)) * ((Bl : ℝ) + 1)) ≤ δ / 3 := by sorry
