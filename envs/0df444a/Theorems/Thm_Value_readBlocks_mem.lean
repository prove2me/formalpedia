-- Prove2me | Theorems.Thm_Value_readBlocks_mem
-- name    : Value.readBlocks_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:22.36845+00:00
-- url     : https://prove2.me/theorems/4145d2f4-83bc-45d0-a145-858ebd703edc
-- title:
--   Value: read Blocks mem
-- statement:
--   «θ_{a,b} ∈ {0,1}^{c_{a,b}}»: what the tables read from one string of L bits per edge is a choice
--   of one string of c_{a,b} bits per pair {a, b} of nodes in different groups.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L87-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L87-L94

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
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Value.readBlocks_mem (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    {Λ : Fin K × Fin K → List Bool} (hΛ : Λ ∈ edgeStrings K L) : readBlocks Np c hK0 x Λ ∈ blockStrings N (Paper.grouping hK0 x) := by sorry
