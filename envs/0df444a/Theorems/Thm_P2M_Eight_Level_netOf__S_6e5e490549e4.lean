-- Prove2me | Theorems.Thm_P2M_Eight_Level_netOf__S_6e5e490549e4
-- name    : P2M_Eight_Level_netOf__S_6e5e490549e4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:30.415706+00:00
-- url     : https://prove2.me/theorems/f5048590-69b7-4e91-be7b-fc60189eba68
-- title:
--   P2 M Eight Level net Of  S 6e5e490549e4: P2 M Eight Level net Of  S 6e5e490549e4
-- statement:
--   «S_a is the set of these tuples, encoded by concatenation in g(g² − 1)λ ≤ P bits, where P =
--   g³λ.» Different from the paper: the settings are all words of exactly g³λ bits, because a setting of
--   a grid point has a dummy string for the grid point
--   itself (see `Eight.eqExpansion`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L89-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L89-L96

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

theorem P2M_Eight_Level_netOf__S_6e5e490549e4 (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (a : Fin (nParts g g tr)) :
    (netOfι g tr lam y Rm).S a = words (g ^ 3 * lam) := by sorry

alias «Eight».«Level».«netOfι_S» := P2M_Eight_Level_netOf__S_6e5e490549e4
