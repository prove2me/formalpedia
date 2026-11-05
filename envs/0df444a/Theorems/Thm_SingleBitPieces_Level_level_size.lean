-- Prove2me | Theorems.Thm_SingleBitPieces_Level_level_size
-- name    : SingleBitPieces.Level.level_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:20.542543+00:00
-- url     : https://prove2.me/theorems/0293841c-33f4-4390-828f-d46bc11d4549
-- title:
--   Level: level size
-- statement:
--   Section 5, proof of Proposition 3, «Cost», the sizes: the sum of the sizes that occur in the
--   loop over the terms is polynomial in sc + B + λ. Not in the paper, which counts operations only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Arith.lean#L37-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/Level/Arith.lean#L37-L79

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
import Definitions.Def_SingleBitPieces_Level_Arith
set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Groundwork
open Arith

theorem SingleBitPieces.Level.level_size (g a A Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M P B' : ℕ, 1 ≤ lam → M ≤ 2 * Rn * lam → P ≤ g ^ 3 * lam →
    B' ≤ (g + 2 * g ^ 2) * (B + lam) →
    2 * sc + 2 * M + g * (P + B') + g * g * B' + 20 + a * (sc + B + lam) ^ a + A * (sc + (M + 1) + P + B') ^ A
      ≤ A2 * (sc + B + lam) ^ A2 := by sorry
