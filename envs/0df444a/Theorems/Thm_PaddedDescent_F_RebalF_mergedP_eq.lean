-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_mergedP_eq
-- name    : PaddedDescent.F.RebalF.mergedP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:00.794114+00:00
-- url     : https://prove2.me/theorems/7e8b5c62-c74e-4ec1-a1da-f91f3ca0b065
-- title:
--   Rebal F: merged P eq
-- statement:
--   The plain value is the specification `mergedVal`, on well-formed queries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L110-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L110-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}

theorem PaddedDescent.F.RebalF.mergedP_eq {K g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g F.toP c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    mergedP K g F ((c, x), (G.val, List.ofFn θ)) = mergedVal K g F.toP N ((c, x), (G.val, List.ofFn θ)) := by sorry
