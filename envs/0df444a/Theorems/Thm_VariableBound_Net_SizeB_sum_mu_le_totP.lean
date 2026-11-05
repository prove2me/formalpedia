-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_sum_mu_le_totP
-- name    : VariableBound.Net.SizeB.sum_mu_le_totP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:33.123627+00:00
-- url     : https://prove2.me/theorems/3dc4812c-4356-4e80-a3ff-6fb546897741
-- title:
--   Size B: sum mu le tot P
-- statement:
--   The numbers μ_(a,b,κ) of the pairs {a, b} with one fixed node a < g add up to at most μ_κ, the
--   sum over all pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L166-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L166-L186

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

theorem VariableBound.Net.SizeB.sum_mu_le_totP {a : ℕ} (ha : a < g) (κ : ℕ) : ∑ b ∈ (range g).erase a, mu g D y a b κ ≤ totP g D y κ := by sorry
