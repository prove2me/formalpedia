-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_length_objs_le
-- name    : VariableBound.Net.Prof.length_objs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:53.874616+00:00
-- url     : https://prove2.me/theorems/7091c932-4ea6-4a74-b305-6bb583b7da61
-- title:
--   Prof: length objs le
-- statement:
--   Step 3: «there are I ≤ r·s̄ incidences»: if every check has at most s clauses, there are at most
--   r·s + m objects.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L380-L387
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L380-L387

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.length_objs_le {D : Dat} {s : ℕ} (hs : ∀ L ∈ D.2, L.length ≤ s) : (objs D).length ≤ D.2.length * s + D.1.length := by sorry
