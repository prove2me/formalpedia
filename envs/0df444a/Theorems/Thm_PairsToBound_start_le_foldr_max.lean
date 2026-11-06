-- Prove2me | Theorems.Thm_PairsToBound_start_le_foldr_max
-- name    : PairsToBound.start_le_foldr_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:55:24.438472+00:00
-- url     : https://prove2.me/theorems/9adf0b2b-4346-477c-ad00-6247ec24cda3
-- title:
--   Pairs To Bound: start le foldr max
-- statement:
--   The maximum of a list, computed from the right with the start value a, is at least a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L38-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Width.lean#L38-L41

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

theorem PairsToBound.start_le_foldr_max (l : List ℕ) (a : ℕ) : a ≤ l.foldr max a := by sorry
