-- Prove2me | Theorems.Thm_VariableBound_Spec_count_spec
-- name    : VariableBound.Spec.count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:20.812923+00:00
-- url     : https://prove2.me/theorems/393d1b63-fdb5-40ce-bdc6-242a8b423bac
-- title:
--   Spec: count spec
-- statement:
--   Let P be closed upwards and hold at some number j ≤ N, and let p decide «not P». Then the number
--   of j < N with p j is the least number at which P holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L53-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L53-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec

theorem VariableBound.Spec.count_spec (P : ℕ → Prop) (p : ℕ → Bool) (N : ℕ) (hp : ∀ j, p j = true ↔ ¬ P j) (up : ∀ j, P j → P (j + 1)) (hN : ∃ j ≤ N, P j) :
    P ((List.range N).filter p).length ∧ ∀ j < ((List.range N).filter p).length, ¬ P j := by sorry
