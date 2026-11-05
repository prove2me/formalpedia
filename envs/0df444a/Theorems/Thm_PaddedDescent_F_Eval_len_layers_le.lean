-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_len_layers_le
-- name    : PaddedDescent.F.Eval.len_layers_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:39.886261+00:00
-- url     : https://prove2.me/theorems/c62a1c56-e0f4-498b-970b-ea2f8653f8c1
-- title:
--   Eval: len layers le
-- statement:
--   A bound on the length of the word of layers, by the number of their clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L179-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L179-L188

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)

theorem PaddedDescent.F.Eval.len_layers_le {k n : ℕ} (Ls : List Fml) (h : WfL k n Ls) : len Ls ≤ Ls.flatten.length * (k * (3 * n + 5) + 10) + 4 * Ls.length + 2 := by sorry
