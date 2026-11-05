-- Prove2me | Theorems.Thm_P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f
-- name    : P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:33.061195+00:00
-- url     : https://prove2.me/theorems/97d20582-ab61-4ed0-8349-db58752c31ce
-- title:
--   P2 M Variable Bound Net Tests sum length tst le  2d95f271980f: P2 M Variable Bound Net Tests sum length tst le  2d95f271980f
-- statement:
--   Step 3, «The total»: T_κ, the number of tests of the objects of kind κ, is at most k − 1 + κ
--   times the number of these objects, if Φ has clauses of at most k literals (`WfD`). Sum over all
--   pairs of numbers below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L175-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L175-L201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f (hW : WfD k n D) (κ : ℕ) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n D p.1 p.2 κ).length else 0) ≤
      (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by sorry

alias «VariableBound».«Net».«Tests».«sum_length_tst_le'» := P2M_VariableBound_Net_Tests_sum_length_tst_le__2d95f271980f
