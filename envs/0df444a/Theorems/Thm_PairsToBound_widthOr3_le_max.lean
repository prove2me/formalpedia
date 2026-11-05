-- Prove2me | Theorems.Thm_PairsToBound_widthOr3_le_max
-- name    : PairsToBound.widthOr3_le_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:56:04.559212+00:00
-- url     : https://prove2.me/theorems/2426753a-eb62-45ab-9c04-7e153a29adac
-- title:
--   Pairs To Bound: width Or3 le max
-- statement:
--   If no clause of φ has more than k literals, the width of Step 6 is at most max(k, 3).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L73-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L73-L76

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

theorem PairsToBound.widthOr3_le_max {n k : ℕ} {φ : CNF n} (h : ∀ C ∈ φ, C.length ≤ k) : widthOr3 φ ≤ max k 3 := by sorry
