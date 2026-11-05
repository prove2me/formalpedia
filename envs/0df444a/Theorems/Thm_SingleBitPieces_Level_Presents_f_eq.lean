-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Presents_f_eq
-- name    : SingleBitPieces.Level.Presents.f_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:00.891458+00:00
-- url     : https://prove2.me/theorems/adee7aad-0d4c-4486-b1db-cd4b7d23833b
-- title:
--   Presents: f eq
-- statement:
--   The plain function for the factors computes the factor of the network, for any pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L81-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L81-L84

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

theorem SingleBitPieces.Level.Presents.f_eq (P : PiecesF) {g : ℕ} (tr : Bool) (ℓ y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * ℓ) (hθ : θ.length = capG P g g tr 0 ℓ y a b) :
    gridFf P [] g g tr 0 ℓ y ((a.val, b.val), (z, θ)) = (gridN P [] g g tr 0 ℓ y Rm).f a b z θ := by sorry
