-- Prove2me | Theorems.Thm_Printed_networkOnSteps_poly
-- name    : Printed.networkOnSteps_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:43:56.839856+00:00
-- url     : https://prove2.me/theorems/2430367c-31d6-4c75-be75-a318edda1bb7
-- title:
--   Printed: network On Steps poly
-- statement:
--   A machine for networks with polynomial-time steps, on a network given by step machines with
--   polynomial-time steps and numbers in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L75-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_HandOver
set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {Q A C : Type}

theorem Printed.networkOnSteps_poly [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : Procs C) (hN : NM.PolyTimeSteps) (h : Np.Keeps) (hP : Unary Np.P) (hB : Unary Np.B) :
    Nonempty (IsPolyT (networkOnSteps g NM Np)) := by sorry
