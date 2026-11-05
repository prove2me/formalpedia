-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_Form_len_le
-- name    : PaddedDescent.F.Eval.Form.len_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:47:46.482536+00:00
-- url     : https://prove2.me/theorems/c7ddc8bc-a229-4a64-9dad-88cf38428e5b
-- title:
--   Form: len le
-- statement:
--   The word of layers of the given form fits under a pad of length layLen k n m R, if they hold at
--   most m clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L192-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L192-L197

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

theorem PaddedDescent.F.Eval.Form.len_le {k n R c m : ℕ} {Ls : List Fml} (h : Form k n R c Ls) (hc : c ≤ m) : len Ls ≤ layLen k n m R := by sorry
