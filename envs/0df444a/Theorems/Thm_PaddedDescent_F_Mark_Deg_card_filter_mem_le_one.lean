-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_card_filter_mem_le_one
-- name    : PaddedDescent.F.Mark.Deg.card_filter_mem_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:03.41581+00:00
-- url     : https://prove2.me/theorems/5a9f057c-131d-4cc3-8d96-0d2f3232a4d9
-- title:
--   Deg: card filter mem le one
-- statement:
--   A literal lies in at most one set of size 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L43-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L43-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_WidthK_Step_card_filter_mem_le_one
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}

theorem PaddedDescent.F.Mark.Deg.card_filter_mem_le_one {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) : (G.filter fun C => y ∈ C).card ≤ 1 := by sorry
