-- Prove2me | Theorems.Thm_PaddedDescent_F_RebalF_presents
-- name    : PaddedDescent.F.RebalF.presents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:47:38.490601+00:00
-- url     : https://prove2.me/theorems/92a32929-ffe7-41f7-9639-56f25205d7b7
-- title:
--   Rebal F: presents
-- statement:
--   How to show that a network of plain functions presents a network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L32-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/RebalF.lean#L32-L44

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
import Theorems.Thm_Groundwork_Prog_presents
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset

theorem PaddedDescent.F.RebalF.presents {C : Type} (F : FNet C) (c : C) {g : ℕ} (N : Network (Fin g) (List Bool) (List Bool))
    (hS : ∀ a : Fin g, N.S a = words (F.n c a))
    (hc : ∀ a b : Fin g, a ≠ b → N.c a b = F.cap c a b)
    (hl : ∀ a b : Fin g, a ≠ b → N.lab a b = words (F.cap c a b))
    (hW : ∀ (a : Fin g) (z : List Bool), z.length = F.n c a → F.W (c, (a.val, z)) = N.W a z)
    (hf : ∀ (a b : Fin g) (z θ : List Bool), a ≠ b → z.length = F.n c a → θ.length = F.cap c a b →
      F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ) :
    F.toP.Presents c N 0 0 := by sorry
