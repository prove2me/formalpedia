-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le_of_wfL
-- name    : PaddedDescent.F.Mark.Deg.length_tch_le_of_wfL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:10.390261+00:00
-- url     : https://prove2.me/theorems/fadcf744-3f14-45ab-9736-03116b52efe6
-- title:
--   Deg: length tch le of wf L
-- statement:
--   At most qv g n · Δ clauses touch a node, for well-formed layers and at least one node, also if
--   there is no variable: then there is no clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L213-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L213-L225

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

theorem PaddedDescent.F.Mark.Deg.length_tch_le_of_wfL {k g n Δ : ℕ} {Ls : List Fml} (hg : 0 < g) (hW : WfL k n Ls) (hx : ∀ v, (occ Ls.flatten v).length ≤ Δ) (a : ℕ) :
    (tch g n Ls a).length ≤ qv g n * Δ := by sorry
