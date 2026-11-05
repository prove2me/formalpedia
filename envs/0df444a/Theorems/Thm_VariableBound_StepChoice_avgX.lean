-- Prove2me | Theorems.Thm_VariableBound_StepChoice_avgX
-- name    : VariableBound.StepChoice.avgX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:13.979896+00:00
-- url     : https://prove2.me/theorems/b8c56c85-f310-4b6d-bbe6-0237e9016348
-- title:
--   Step Choice: avg X
-- statement:
--   Step 2, «the average of X(𝓛, Γ_u) over u ∈ Ω is at most (3/4)·X(𝓛)», for a family as in Lemma 13
--   with v = n̄.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L106-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L106-L122

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

theorem VariableBound.StepChoice.avgX (V : X → Finset E) (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hF : IsFamily nb Ω Γ) :
    4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u]) ≤ 3 * #Ω * Xsum V nb L := by sorry
