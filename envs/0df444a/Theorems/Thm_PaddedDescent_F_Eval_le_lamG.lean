-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_le_lamG
-- name    : PaddedDescent.F.Eval.le_lamG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:42.240416+00:00
-- url     : https://prove2.me/theorems/dcf655c6-d80e-443b-82ff-8e1915c34f8a
-- title:
--   Eval: le lam G
-- statement:
--   x ≤ lamG K g Ub₀ P if K³·x ≤ K³ + K·U + g·P' with U ≤ Ub₀ and P' ≤ P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L32-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L32-L38

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

theorem PaddedDescent.F.Eval.le_lamG {K g x Uv Pv Ub₀ P : ℕ} (hK : 0 < K) (h : K ^ 3 * x ≤ K ^ 3 + K * Uv + g * Pv) (hU : Uv ≤ Ub₀) (hP : Pv ≤ P) :
    x ≤ lamG K g Ub₀ P := by sorry
