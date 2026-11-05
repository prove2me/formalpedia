-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_length_occ_le
-- name    : PaddedDescent.F.Mark.Deg.length_occ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:23.1696+00:00
-- url     : https://prove2.me/theorems/eeb9cfb2-0535-4a5a-b88c-52a94683dc26
-- title:
--   Deg: length occ le
-- statement:
--   In a list in normal form, the clauses with the variable v are at most those with the literal v
--   and those with the literal ¬v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L80-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L80-L95

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

theorem PaddedDescent.F.Mark.Deg.length_occ_le {x : PFml} (hx : NF x) (v : ℕ) :
    (occ x v).length ≤ ((toFin x).filter fun C => (v, true) ∈ C).card + ((toFin x).filter fun C => (v, false) ∈ C).card := by sorry
