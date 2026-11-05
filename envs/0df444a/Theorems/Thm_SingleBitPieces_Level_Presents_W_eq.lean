-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Presents_W_eq
-- name    : SingleBitPieces.Level.Presents.W_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:22.915741+00:00
-- url     : https://prove2.me/theorems/1c6976b8-40b3-43ad-a636-3cb6b8494ebb
-- title:
--   Presents: W eq
-- statement:
--   What the procedure for the weights (`sideWv` with `sideChk`) computes is the weight of the
--   network, for any pieces.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L53-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L53-L78

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

theorem SingleBitPieces.Level.Presents.W_eq (P : PiecesF) {C : Type} {g : ℕ} (tr : Bool) (lam : C → ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (c : C) (y : ℕ) (a : Fin (nParts g g tr))
    {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam c) :
    (gridN P [] g g tr 0 (lam c) y Rm).W a z = sideWv g tr (lam c) Rm (sideChk g tr lam ((c, y), (a.val, z))) a z := by sorry
