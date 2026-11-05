-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Presents_time_W
-- name    : SingleBitPieces.Level.Presents.time_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:45.361171+00:00
-- url     : https://prove2.me/theorems/65fabf71-a514-4ee7-a526-7a4a66112355
-- title:
--   Presents: time W
-- statement:
--   The steps of the weights.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L99-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L99-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_ClauseBound_Alg_Grid
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_Level_Presents
set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents

theorem SingleBitPieces.Level.Presents.time_W (g B lm : ℕ) {t : ℕ} (hl : 1 ≤ lm) (ht : 1 ≤ t) : g * (t + 1) ≤ sideA g * (B + lm) ^ sideA g * t := by sorry
