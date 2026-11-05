-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_length_markPar
-- name    : PaddedDescent.F.Top.length_markPar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:08.377705+00:00
-- url     : https://prove2.me/theorems/11332f65-5165-4ba5-bcd2-47239cfa9aa6
-- title:
--   Top: length mark Par
-- statement:
--   The four parameters of the evaluations, as numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L155-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L155-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.length_markPar (n s : ℕ) : (markPar n s).1.length = n ∧ (markPar n s).2.1.length = n + 2 ∧ (markPar n s).2.2.1.length = betaOf s ∧
    (markPar n s).2.2.2.length = 2 ^ betaOf s := by sorry
