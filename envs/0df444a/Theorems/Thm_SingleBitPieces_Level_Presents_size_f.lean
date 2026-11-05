-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Presents_size_f
-- name    : SingleBitPieces.Level.Presents.size_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:28:14.758309+00:00
-- url     : https://prove2.me/theorems/3422b598-1a54-41c1-883f-4577f47327e0
-- title:
--   Presents: size f
-- statement:
--   The sizes of the factors: the query, and the value with at most g·B + 2g²λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L113-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L113-L134

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents

theorem SingleBitPieces.Level.Presents.size_f {C : Type} [HasSize C] (g B S lm : ℕ) (hl : 1 ≤ lm) (c : C) {y a b : ℕ} {z θ : List Bool} {v : ℤ}
    (hy : y < (lm + 1) ^ nRect g) (ha : a < g) (hb : b < g) (hz : z.length = g ^ 3 * lm) (hθ : θ.length ≤ g ^ 2 * lm)
    (hv : |v| ≤ 2 ^ (g * B + g ^ 2 * (2 * lm))) :
    max (size ((c, y), ((a, b), (z, θ)))) (size v) + 1 ≤ S + sideA g * (size c + B + lm) ^ sideA g := by sorry
