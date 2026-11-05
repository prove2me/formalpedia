-- Prove2me | Theorems.Thm_Printed_networkOn_poly
-- name    : Printed.networkOn_poly
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:46:34.734526+00:00
-- url     : https://prove2.me/theorems/fc49451f-cd06-479e-8116-decc54ed6e8e
-- title:
--   Printed: network On poly
-- statement:
--   The same on a network given by procedures that have query access of their own.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L84-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/HandOver.lean#L84-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_HandOver
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem

set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {Q A C : Type}

theorem Printed.networkOn_poly [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (hN : NM.PolyTimeSteps)
    (hP : Unary Np.P) (hB : Unary Np.B) (hl : Unary fun p : C × ℕ => Np.len p.1 p.2) (hc : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2)
    (hm : Np.mem.PolyTimeSteps) (hW : Np.W.PolyTimeSteps) (hΨ : Np.Ψ.PolyTimeSteps) (hf : Np.f.PolyTimeSteps) : (networkOn g NM Np).PolyTimeSteps := by sorry
