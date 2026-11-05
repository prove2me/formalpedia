-- Prove2me | Theorems.Thm_P2M_Eight_Level_Z__digOf_6fd272fe669a
-- name    : P2M_Eight_Level_Z__digOf_6fd272fe669a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:13.778307+00:00
-- url     : https://prove2.me/theorems/589f199f-0eea-4bf6-84a1-8ee0e5773bd4
-- title:
--   P2 M Eight Level Z  dig Of 6fd272fe669a: P2 M Eight Level Z  dig Of 6fd272fe669a
-- statement:
--   Z_ι depends only on the values of ι on ℛ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L55-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}

theorem P2M_Eight_Level_Z__digOf_6fd272fe669a (W : Inst (Fin g × Fin g) (Bits lam)) (y : ℕ) : Zι W (digOf g lam y) = Zι W (Eight.Level.patOf g lam y) := by sorry

alias «Eight».«Level».«Zι_digOf» := P2M_Eight_Level_Z__digOf_6fd272fe669a
