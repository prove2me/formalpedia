-- Prove2me | Theorems.Thm_PairsToBound_mem_le_foldr_max
-- name    : PairsToBound.mem_le_foldr_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:55:39.458952+00:00
-- url     : https://prove2.me/theorems/eb0a1299-22c6-4243-b6a2-5480965d7085
-- title:
--   Pairs To Bound: mem le foldr max
-- statement:
--   The maximum of a list, computed from the right with any start value, is at least every member of
--   the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L45-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L45-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)

theorem PairsToBound.mem_le_foldr_max {l : List ℕ} {a x : ℕ} (h : x ∈ l) : x ≤ l.foldr max a := by sorry
