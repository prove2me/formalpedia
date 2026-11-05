-- Prove2me | Theorems.Thm_Paper_grouped_value
-- name    : Paper.grouped_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:39.259764+00:00
-- url     : https://prove2.me/theorems/50b61137-425f-4bb7-b8db-a239b7b68e2f
-- title:
--   Paper: grouped value
-- statement:
--   "… so the value equals Z": the (K, L)-clique with the tables W̃ has the value of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L178-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L178-L184

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset
open NetE Stepped
variable {C : Type} {g K : ℕ}

theorem Paper.grouped_value (Np : NetworkProcedures C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hK0 : 0 < K) (hN : IsNetwork Np c N P B τ S) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) :
    cliqueValue L (groupedTables Np c N hK0 x L) = N.value := by sorry
