-- Prove2me | Theorems.Thm_VariableBound_StepChoice_minUps
-- name    : VariableBound.StepChoice.minUps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:42:10.603434+00:00
-- url     : https://prove2.me/theorems/a6e9ae11-f7f9-458c-8f64-af983f550a11
-- title:
--   Step Choice: min Ups
-- statement:
--   Step 2, «and so is the minimum»: under the hypotheses of `avgUps`, a list (𝓛, Γ_u), u ∈ Ω, with
--   the smallest Υ has Υ(𝓛, Γ_u) ≤ Υ(𝓛).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L183-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L183-L189

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

theorem VariableBound.StepChoice.minUps (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) (u : ι) (hu : u ∈ Ω) (hmin : ∀ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb (L ++ [Γ u'])) :
    Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb L := by sorry
