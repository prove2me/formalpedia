-- Prove2me | Theorems.Thm_VariableBound_StepChoice_avgUps
-- name    : VariableBound.StepChoice.avgUps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:15.22194+00:00
-- url     : https://prove2.me/theorems/0b86744c-8ae8-45c6-a83e-8ab94c04fd63
-- title:
--   Step Choice: avg Ups
-- statement:
--   Step 2, «the average of Υ(𝓛, Γ_u) is at most Υ(𝓛)», for a list of fewer than r̄ checks and a
--   family as in Lemma 13 with v = n̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L155-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L155-L179

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_StepChoice
set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem VariableBound.StepChoice.avgUps (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) : ∑ u ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ #Ω * Ups V nb β rb tb L := by sorry
