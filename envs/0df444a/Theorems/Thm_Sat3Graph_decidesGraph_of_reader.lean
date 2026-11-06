-- Prove2me | Theorems.Thm_Sat3Graph_decidesGraph_of_reader
-- name    : Sat3Graph.decidesGraph_of_reader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:39:07.386627+00:00
-- url     : https://prove2.me/theorems/716169d8-d382-41e0-8435-288507639727
-- title:
--   Sat3 Graph: decides Graph of reader
-- statement:
--   Let `askSized gates D` answer at width 2 as `StAskSized` says, with the constant c'. Let the
--   reader rd hand over, on the code of (G, s) with s ≤ n, some (n in unary, s', ψ) with s' ≤ n and ψ of
--   width 2 on x₀ … xₙ₋₁, such that ψ has a satisfying assignment with exactly s' true variables exactly
--   if p holds of (G, s). Then `askSized gates D` behind rd decides p with the same constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Sets.lean#L35-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Sets.lean#L35-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_Sat3Graph_Ask
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Read
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Sets
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat

theorem Sat3Graph.decidesGraph_of_reader {gates : ℕ → ℕ → List CircuitLowerBound.GateD} {D : StepMachine (List Unit × Fml) Bool} {δ : ℝ} {c' : ℕ}
    (hA : ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped 2 n ψ → (2 - 3) * ψ.length ≤ 0 * (n + 1) →
      ∃ (T : ℕ) (b : Bool), (askSized gates D).Runs (List.replicate n (), s, ψ) T (c' * (n + 2) ^ c') b ∧ (b = true ↔ cntS n s ψ ≠ 0) ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n))
    (rd : List Bool → List Unit × ℕ × Fml) (p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ (s' : ℕ) (ψ : Fml), s' ≤ n ∧ Shaped 2 n ψ ∧
      rd (codeWith G s) = (List.replicate n (), s', ψ) ∧ (cntS n s' ψ ≠ 0 ↔ p n G s)) :
    DecidesGraph (Stepped.mapIn rd (askSized gates D)) p δ c' := by sorry
