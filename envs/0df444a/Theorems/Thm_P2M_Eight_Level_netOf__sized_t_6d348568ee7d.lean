-- Prove2me | Theorems.Thm_P2M_Eight_Level_netOf__sized_t_6d348568ee7d
-- name    : P2M_Eight_Level_netOf__sized_t_6d348568ee7d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:56:32.708741+00:00
-- url     : https://prove2.me/theorems/ac5f635d-5c6b-46fb-9259-90cfed83f87c
-- title:
--   P2 M Eight Level net Of  sized t 6d348568ee7d: P2 M Eight Level net Of  sized t 6d348568ee7d
-- statement:
--   Both networks that the algorithm runs satisfy conditions (i) and (ii) of Definition 2 with P =
--   g³λ and all values at most 2^{gB + g²t}; this is the form that the proof of the cost of a level
--   uses. From `Eight.rowNetwork_sized_t` and
--   `Eight.colNetwork_sized_t`. `BoundedInst lam B Rm`: the tables are at most 2^B in absolute value at
--   the queries that are asked.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L119-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L119-L126

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

theorem P2M_Eight_Level_netOf__sized_t_6d348568ee7d {B : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst lam B Rm) :
    (netOfι g tr lam y Rm).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by sorry

alias «Eight».«Level».«netOfι_sized_t» := P2M_Eight_Level_netOf__sized_t_6d348568ee7d
