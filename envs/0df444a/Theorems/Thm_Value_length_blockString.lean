-- Prove2me | Theorems.Thm_Value_length_blockString
-- name    : Value.length_blockString
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:46.530224+00:00
-- url     : https://prove2.me/theorems/25ba5d24-049b-44cf-8583-d33a632a2d0c
-- title:
--   Value: length block String
-- statement:
--   A string θ_{a,b} of a choice of blocks has as many bits as the procedures say, whichever of a, b
--   is the smaller.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L99-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L99-L107

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

theorem Value.length_blockString (h : IsNetworkP Np c N P B τ S) {χ : Fin g → Fin K} {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N χ) {a b : Fin g} (hne : χ a ≠ χ b) :
    (θ (pr a b)).length = Np.cap c a b := by sorry
