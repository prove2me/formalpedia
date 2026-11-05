-- Prove2me | Theorems.Thm_Value_mem_mD_iff
-- name    : Value.mem_mD_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:25.453309+00:00
-- url     : https://prove2.me/theorems/5f352544-1bc8-4a12-81b3-a5236ce540a8
-- title:
--   Value: mem m D iff
-- statement:
--   The strings of L bits whose bits after the last block are 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L111-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L111-L113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Value.mem_mD_iff (Nq : PNet C) (c : C) (x L : ℕ) (G G' : Fin K) (w : List Bool) :
    w ∈ mD K g Nq c x L G G' ↔ w.length = L ∧ ∀ bit ∈ w.drop (lbLen K g Nq c x G G'), bit = false := by sorry
