-- Prove2me | Theorems.Thm_SingleBitPieces_Level_Pieces_sum_ofFn
-- name    : SingleBitPieces.Level.Pieces.sum_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:28:50.656657+00:00
-- url     : https://prove2.me/theorems/2301fd5f-3fae-4346-b40c-91c230a6566a
-- title:
--   Pieces: sum of Fn
-- statement:
--   A sum over θ ∈ {0,1}^c, written as functions, is the sum over the words of c bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Pieces.lean#L32-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Pieces.lean#L32-L36

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
import Definitions.Def_PaddedDescent_F_FuelCert
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_Level_Pieces
set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset
open SingleBitPieces.Level.Pieces

theorem SingleBitPieces.Level.Pieces.sum_ofFn (c : ℕ) (G : List Bool → ℤ) : ∑ θ : Fin c → Bool, G (List.ofFn θ) = ∑ w ∈ words c, G w := by sorry
