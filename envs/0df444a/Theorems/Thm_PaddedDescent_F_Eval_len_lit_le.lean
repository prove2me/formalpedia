-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_len_lit_le
-- name    : PaddedDescent.F.Eval.len_lit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:27.926391+00:00
-- url     : https://prove2.me/theorems/8b97a083-ce79-4b73-bd0f-a97537d9eac1
-- title:
--   Eval: len lit le
-- statement:
--   A bound on the length of the word of a literal with variable below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L171-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L171-L176

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

theorem PaddedDescent.F.Eval.len_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : len l + 2 ≤ 3 * n + 5 := by sorry
