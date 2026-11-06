-- Prove2me | Theorems.Thm_PairsToBound_foldr_max_le
-- name    : PairsToBound.foldr_max_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:55:33.49267+00:00
-- url     : https://prove2.me/theorems/0f78421a-4d91-4f70-81a8-1e3a5fe1d302
-- title:
--   Pairs To Bound: foldr max le
-- statement:
--   A number that is at least the start value and at least every member of the list is at least the
--   maximum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L56-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L56-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le

set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)

theorem PairsToBound.foldr_max_le {l : List ℕ} {a b : ℕ} (ha : a ≤ b) (h : ∀ x ∈ l, x ≤ b) : l.foldr max a ≤ b := by sorry
