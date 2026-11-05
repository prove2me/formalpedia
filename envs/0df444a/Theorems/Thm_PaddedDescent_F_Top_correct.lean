-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_correct
-- name    : PaddedDescent.F.Top.correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:59:42.208041+00:00
-- url     : https://prove2.me/theorems/d50e5d8e-a26f-428a-b87c-f754c5342c0a
-- title:
--   Top: correct
-- statement:
--   The function `A` is correct on every instance with sOf n ≥ s0K 3, given the pad of length 2^(C0K
--   3·(n / 2^(sOf n) + 1)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L188-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L188-L224

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
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.correct (hCount : StCountM) (hLf : StLeaf) (hSched : StSched) (hA : StA) (hAW : StAW) : StCorrect (C0K 3) (s0K 3) := by sorry
