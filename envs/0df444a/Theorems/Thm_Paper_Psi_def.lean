-- Prove2me | Theorems.Thm_Paper_Psi_def
-- name    : Paper.Psi_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:24.172432+00:00
-- url     : https://prove2.me/theorems/b50e54f8-3244-417a-96da-441da7f43c45
-- title:
--   Paper: Psi def
-- statement:
--   Ψ_ab(z, z') = Σ_θ f_ab(z, θ) · f_ba(z', θ) (Definition 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L43-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecNetworks_Networks.lean#L43-L44

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

theorem Paper.Psi_def {J σ τ : Type*} [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) :
    N.Ψ a b z z' = ∑ θ ∈ N.lab a b, N.f a b z θ * N.f b a z' θ := by sorry
