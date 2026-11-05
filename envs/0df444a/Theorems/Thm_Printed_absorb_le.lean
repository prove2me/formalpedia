-- Prove2me | Theorems.Thm_Printed_absorb_le
-- name    : Printed.absorb_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:43:37.722357+00:00
-- url     : https://prove2.me/theorems/a7ac7c30-bc3c-461b-abe3-1f522cde254d
-- title:
--   Printed: absorb le
-- statement:
--   The same for any s and y that are at most k·x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L33-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L33-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_Printed_Absorb
set_option autoImplicit false
section
section
open Printed

theorem Printed.absorb_le (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x s y : ℕ, 1 ≤ x → s ≤ k * x → y ≤ k * x → s + a * y ^ a ≤ Cc * x ^ Cc := by sorry
