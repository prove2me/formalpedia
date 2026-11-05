-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_prog
-- name    : PaddedDescent.F.Top.prog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:33.318585+00:00
-- url     : https://prove2.me/theorems/27ae447c-8b12-4aec-bddc-e6c08bee80d1
-- title:
--   Top: prog
-- statement:
--   The sparsification lemma of the imported modules `SparsifyWidthK.Step` to
--   `SparsifyWidthK.ProgMain`, for the program `stepK`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L104-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L104-L106

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

theorem PaddedDescent.F.Top.prog : WidthK.StProg := by sorry
