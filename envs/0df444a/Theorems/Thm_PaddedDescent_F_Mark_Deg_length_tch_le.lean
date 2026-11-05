-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le
-- name    : PaddedDescent.F.Mark.Deg.length_tch_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:52:12.223554+00:00
-- url     : https://prove2.me/theorems/9462038f-eae1-49c5-bfe2-daff85ed12da
-- title:
--   Deg: length tch le
-- statement:
--   If every variable occurs in at most Δ clauses of the layers, at most qv g n · Δ of these clauses
--   touch the node a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L195-L206
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L195-L206

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

theorem PaddedDescent.F.Mark.Deg.length_tch_le {g n Δ : ℕ} {Ls : List Fml} (hq : 0 < qv g n) (hx : ∀ v, (occ Ls.flatten v).length ≤ Δ) (a : ℕ) :
    (tch g n Ls a).length ≤ qv g n * Δ := by sorry
