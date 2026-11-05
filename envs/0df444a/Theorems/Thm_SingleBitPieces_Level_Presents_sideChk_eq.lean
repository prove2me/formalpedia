-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Presents_sideChk_eq
-- name    : SingleBitPieces.Level.Presents.sideChk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:26.621767+00:00
-- url     : https://prove2.me/theorems/a462eb93-549e-43e8-b001-50108103a3a5
-- title:
--   Presents: side Chk eq
-- statement:
--   The test of the procedure `sideChk` for the weights is the test of the grid with g rows and g
--   columns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L45-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Presents.lean#L45-L49

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

theorem SingleBitPieces.Level.Presents.sideChk_eq {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ) (c : C) (y a : ℕ) (z : List Bool) :
    sideChk g tr lam ((c, y), (a, z)) = chkG g g tr (lam c) (a, z) := by sorry
