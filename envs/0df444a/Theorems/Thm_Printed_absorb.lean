-- Prove2me | Theorems.Thm_Printed_absorb
-- name    : Printed.absorb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T17:43:38.321098+00:00
-- url     : https://prove2.me/theorems/b5bac68d-d2ca-4e44-99e1-64fb8772303d
-- title:
--   Printed: absorb
-- statement:
--   For all a and k there is Cc ≥ a with k·x + a·(k·x)^a ≤ Cc·x^Cc for all x ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L23-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L23-L30

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

theorem Printed.absorb (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x : ℕ, 1 ≤ x → k * x + a * (k * x) ^ a ≤ Cc * x ^ Cc := by sorry
