-- Prove2me | Theorems.Thm_PaddedDescent_Col_exists_colouring_cap_nat
-- name    : PaddedDescent.Col.exists_colouring_cap_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:54.824404+00:00
-- url     : https://prove2.me/theorems/9a4605a8-7309-4827-b01d-9c3597b7b84d
-- title:
--   Col: exists colouring cap nat
-- statement:
--   The same lemma for `Fin g`, `Fin K`, with a hypothesis in natural numbers: 4·D²·m·K ≤ g and
--   (g+2)·K < 2^m for some m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L310-L334
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L310-L334

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Definitions.Def_PaddedDescent_Col_Colouring
set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem PaddedDescent.Col.exists_colouring_cap_nat {K g : ℕ} (hK : 1 ≤ K) (c : Fin g → Fin g → ℕ) (M D m : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D)
    (hM : ∀ a b, c a b ≤ M) (h1 : 4 * D ^ 2 * m * K ≤ g) (h2 : (g + 2) * K < 2 ^ m) :
    ∃ χ : Fin g → Fin K, (∀ G, K * #{a | χ a = G} < 2 * g) ∧
      ∀ G G', D * K ^ 2 * ∑ a with χ a = G, ∑ b with χ b = G', c a b ≤ D * (∑ a, ∑ b, c a b) + 3 * g ^ 2 * M := by sorry
