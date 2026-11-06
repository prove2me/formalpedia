-- Prove2me | Theorems.Thm_SatFree_inTimeRand_of_inTime
-- name    : SatFree.inTimeRand_of_inTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:48:52.353659+00:00
-- url     : https://prove2.me/theorems/e04c1e68-e660-4440-a8cf-11a461825851
-- title:
--   Sat Free: in Time Rand of in Time
-- statement:
--   If a deterministic algorithm decides k-SAT in time O(2^{δn}), so does a randomized algorithm
--   with error at most p, for every p ≥ 0: the same machine, with no random bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L65-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Random.lean#L65-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal

theorem SatFree.inTimeRand_of_inTime {p : ℝ} (hp : 0 ≤ p) {k : ℕ} {δ : ℝ≥0} (h : InTime k δ) : InTimeRand p k δ := by sorry
