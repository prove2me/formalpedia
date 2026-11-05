-- Prove2me | Theorems.Thm_VariableBound_StepChoice_reached
-- name    : VariableBound.StepChoice.reached
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:42:51.354892+00:00
-- url     : https://prove2.me/theorems/39360abb-7f64-46ca-88fb-3e149f2cc068
-- title:
--   Step Choice: reached
-- statement:
--   Step 2, «every list that is reached has Υ(𝓛) ≤ 2», together with r ≤ r̄. Hypotheses: at most 2^n
--   assignments, n̄ ≥ 1, β, r̄, t̄ as in the text, a family as in Lemma 13 with v = n̄.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L274-L282
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L274-L282

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

theorem VariableBound.StepChoice.reached (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hX : Fintype.card X ≤ 2 ^ n) (hnb : 1 ≤ nb)
    (hrb : IsRb (beta n (Fintype.card E) nb) rb) (htb : IsTb (Fintype.card E) nb rb tb) (hF : IsFamily nb Ω Γ)
    (hL : Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L) : L.length ≤ rb ∧ Ups V nb (beta n (Fintype.card E) nb) rb tb L ≤ 2 := by sorry
