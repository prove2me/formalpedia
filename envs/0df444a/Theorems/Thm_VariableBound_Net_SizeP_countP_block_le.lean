-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_countP_block_le
-- name    : VariableBound.Net.SizeP.countP_block_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:24.521493+00:00
-- url     : https://prove2.me/theorems/ea50bf60-ba8f-4daf-98e7-013dbcde1715
-- title:
--   Size P: count P block le
-- statement:
--   A clause with a variable among a·q, …, a·q + q − 1 is counted at one of these variables (0 < q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L41-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L41-L58

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
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_PaddedDescent_F_Mark_Deg_countP_block_le
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.countP_block_le {q : ℕ} (hq : 0 < q) (a : ℕ) (L : Fml) :
    L.countP (fun C => C.any fun l => l.1 / q == a) ≤ ∑ r ∈ range q, L.countP fun C => C.any fun l => l.1 == a * q + r := by sorry
