-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_sum_home_le
-- name    : VariableBound.Net.SizeP.sum_home_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:57.858851+00:00
-- url     : https://prove2.me/theorems/337f2587-e4f2-4def-b163-717333291108
-- title:
--   Size P: sum home le
-- statement:
--   Step 3, «The parameters»: «the checks with home a give at most ⌈r̄/g⌉·s̄ more», if 0 < g, 0 ≤
--   s̄, r ≤ r̄ and |Λ_j| ≤ s̄ for all j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L265-L274
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L265-L274

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.sum_home_le (hg : 0 < g) {rb : ℕ} {sb : ℚ} (hsb : 0 ≤ sb) (hr : D.2.length ≤ rb) (hs : ∀ L ∈ D.2, (L.length : ℚ) ≤ sb) (a : ℕ) :
    ((∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length : ℕ) : ℚ) ≤ (qv g rb : ℚ) * sb := by sorry
