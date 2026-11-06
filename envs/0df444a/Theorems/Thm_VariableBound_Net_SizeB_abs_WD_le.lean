-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_abs_WD_le
-- name    : VariableBound.Net.SizeB.abs_WD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:19.495959+00:00
-- url     : https://prove2.me/theorems/93b78bf3-12fa-45c5-ba28-29b399556d73
-- title:
--   Size B: abs WD le
-- statement:
--   Step 3, «The parameters»: «condition (ii) holds with B = (k + 1)M + 1», for the weights: |W_a(z)|
--   ≤ 2^B for g > 0 nodes, well-formed data, an admissible profile y, every node a < g and every word z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L246-L258
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L246-L258

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeB
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.abs_WD_le {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ} (_hg : 0 < g) (hW : WfD k n D) (h : admD k g n nb M D fl y = true) {a : ℕ} (ha : a < g)
    (z : List Bool) : |WD g n D y fl a z| ≤ 2 ^ BD k M := by sorry
