-- Prove2me | Theorems.Thm_Printed_subst_within_of
-- name    : Printed.subst_within_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:58.402181+00:00
-- url     : https://prove2.me/theorems/f162b15c-6a2a-4c77-8d98-1a3459517e10
-- title:
--   Printed: subst within of
-- statement:
--   **Answering each query by computing the entry.** M takes at most T operations, a query counted
--   as one; N answers each query within E operations at the prices w'. Then M with its queries answered
--   by N takes at most T·(E + 2) operations at the prices w'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L42-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/GroupingRun.lean#L42-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine

theorem Printed.subst_within_of (hSub : StSubst) {Q A Q' A' C α β : Type} [HasSize C] (M : QueryMachine Q A α β) (N : QueryMachine Q' A' (C × Q) A) (O : Q → Option A) (O' : Q' → Option A') (w' : Q' → ℕ)
    (c : C) (a : α) (T S S' E : ℕ) (b : β) (hM : M.Within O unitCost a T S b) (hN : ∀ x v, O x = some v → N.Within O' w' (c, x) E S' v) :
    (M.subst N).Within O' w' (c, a) (T * (E + 2)) (size c + S + S' + 1) b := by sorry
