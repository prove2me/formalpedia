-- Prove2me | Theorems.Thm_PaddedDescent_F_Eval_val_core
-- name    : PaddedDescent.F.Eval.val_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:37.749068+00:00
-- url     : https://prove2.me/theorems/f38d866c-ad18-4188-a4c9-f70b4e2d8001
-- title:
--   Eval: val core
-- statement:
--   `StValF` with the numbers K and g of nodes as free variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L41-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Eval.lean#L41-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)

theorem PaddedDescent.F.Eval.val_core (hR : StR) (hD : StD) {C : Type} (F : FNet C) (c : C) (pad : U) (sched : List Lvl) (K g Ub₀ P : ℕ) (hg : g = 3 * K ^ 8)
    (N : Network (Fin g) (List Bool) (List Bool)) (hK : 2 ≤ K) (chain : Chain K sched) (col : K ^ g ≤ pad.length)
    (st : 2 ^ (P * (2 * g / K)) ≤ pad.length) (lab : 2 ^ P ≤ pad.length) (tab : 2 ^ ((K - 1) * lamG K g Ub₀ P) ≤ pad.length)
    (fits : Fits pad.length K (lamG K g Ub₀ P) (P * (2 * g / K)) 1 sched) (hN : F.toP.Presents c N 0 0) (hS : N.Sized P 0)
    (hU : N.U ≤ Ub₀) : ((rebalF pad K g F c).elim 0 fun I => ((descend pad sched I).map (bruteF pad 256)).sum) = N.value := by sorry
