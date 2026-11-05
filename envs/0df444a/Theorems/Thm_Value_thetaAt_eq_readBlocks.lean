-- Prove2me | Theorems.Thm_Value_thetaAt_eq_readBlocks
-- name    : Value.thetaAt_eq_readBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:25.068009+00:00
-- url     : https://prove2.me/theorems/aa58c339-fbe5-4af3-9e60-5f0e0553a473
-- title:
--   Value: theta At eq read Blocks
-- statement:
--   «so θ_{a,b} = θ_{b,a}»: whichever of the two tables reads it, the string that is read for the
--   nodes a, b in different groups is the one that `readBlocks` has at the pair {a, b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L73-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L73-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}

theorem Value.thetaAt_eq_readBlocks (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) {a b : Fin g}
    (hne : Paper.grouping hK0 x a ≠ Paper.grouping hK0 x b) :
    thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x a)) a b = readBlocks Np c hK0 x Λ (pr a b) := by sorry
