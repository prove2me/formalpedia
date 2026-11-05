-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_nProf_le
-- name    : PaddedDescent.F.Eval.nProf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:47:56.620402+00:00
-- url     : https://prove2.me/theorems/a90a6b9b-9119-418f-a5d7-81e6fdf98aa5
-- title:
--   Eval: n Prof le
-- statement:
--   The number of profile numbers grows with the number of clauses and of layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L89-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L89-L91

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

theorem PaddedDescent.F.Eval.nProf_le (g : ℕ) {M M' R R' : ℕ} (hM : M ≤ M') (hR : R ≤ R') : nProf g M R ≤ nProf g M' R' := by sorry
