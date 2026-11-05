-- Prove2me | Theorems.Thm_PairsToBound_length_le_widthOr3
-- name    : PairsToBound.length_le_widthOr3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:54:31.966414+00:00
-- url     : https://prove2.me/theorems/a72da277-e22b-4da6-9ff5-1f56a09e48c3
-- title:
--   Pairs To Bound: length le width Or3
-- statement:
--   No clause has more literals than the width of Step 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L69-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L69-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)

theorem PairsToBound.length_le_widthOr3 {n : ℕ} {φ : CNF n} {C : List (Sat3.Lit n)} (h : C ∈ φ) : C.length ≤ widthOr3 φ := by sorry
