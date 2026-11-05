-- Prove2me | Theorems.Thm_VariableBound_Spec_length_filter_range
-- name    : VariableBound.Spec.length_filter_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:22.42505+00:00
-- url     : https://prove2.me/theorems/8a5d6ee2-0c19-4fc1-a6e7-bd7df63f3beb
-- title:
--   Spec: length filter range
-- statement:
--   If p holds below N exactly at the numbers below k, it holds at min N k numbers below N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L33-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L33-L49

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

theorem VariableBound.Spec.length_filter_range (p : ℕ → Bool) (N k : ℕ) (h : ∀ j < N, (p j = true ↔ j < k)) : ((List.range N).filter p).length = min N k := by sorry
