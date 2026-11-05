-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_stEval
-- name    : PaddedDescent.F.Eval.stEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:43.879936+00:00
-- url     : https://prove2.me/theorems/823a3f20-dea6-47db-a85a-8e909b35fa17
-- title:
--   Eval: st Eval
-- statement:
--   One evaluation is exact if the pad is long enough.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L94-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L94-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)

theorem PaddedDescent.F.Eval.stEval (hV : StValF) (hP : StMarkPresents) (hSum : StMarkSum) (hSz : StMarkSized) : StEval := by sorry
