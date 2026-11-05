-- Prove2me | Theorems.Thm_Value_blocks_iff
-- name    : Value.blocks_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:41.45272+00:00
-- url     : https://prove2.me/theorems/35c72caa-3b6c-4398-a259-45ce97d03133
-- title:
--   Value: blocks iff
-- statement:
--   The three conditions on Λ (one string of L bits per edge; all appended bits are 0; the tables
--   read θ from Λ), said edge by edge. The hypothesis `hSB` says that the two tables at an edge read the
--   same block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L135-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L135-L170

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

theorem Value.blocks_iff (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x L : ℕ) {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N (Paper.grouping hK0 x)) (Λ : Fin K × Fin K → List Bool) :
    (Λ ∈ edgeStrings K L ∧ AppendedZero g Np c x Λ ∧ readBlocks Np c hK0 x Λ = θ) ↔ ∀ p, EdgeReads Np c hK0 x L θ p (Λ p) := by sorry
