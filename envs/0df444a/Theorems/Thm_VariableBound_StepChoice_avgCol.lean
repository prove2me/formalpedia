-- Prove2me | Theorems.Thm_VariableBound_StepChoice_avgCol
-- name    : VariableBound.StepChoice.avgCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:16.737903+00:00
-- url     : https://prove2.me/theorems/3af751d7-5f3b-4470-978b-987acba8affb
-- title:
--   Step Choice: avg Col
-- statement:
--   Step 2, «the average of 2^[E ∈ Γ_u] is at most 1 + p», for a family as in Lemma 13 with v = n̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L128-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L128-L142

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

theorem VariableBound.StepChoice.avgCol (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (e : E) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ) :
    ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) ≤ (1 + pp nb) * #Ω := by sorry
