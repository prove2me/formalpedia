-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_countP_block_le
-- name    : PaddedDescent.F.Mark.Deg.countP_block_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:33.677072+00:00
-- url     : https://prove2.me/theorems/9679fc85-fd07-48e4-b269-594c023ffd8b
-- title:
--   Deg: count P block le
-- statement:
--   A clause with a variable among a·q, …, a·q + q − 1 is counted at one of these variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L174-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L174-L191

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
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

theorem PaddedDescent.F.Mark.Deg.countP_block_le {q : ℕ} (hq : 0 < q) (a : ℕ) (L : Fml) :
    L.countP (fun C => C.any fun l => l.1 / q == a) ≤ ∑ r ∈ range q, L.countP fun C => C.any fun l => l.1 == a * q + r := by sorry
