-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_pw_le
-- name    : PaddedDescent.F.Mark.Prof.sum_pw_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:08.131585+00:00
-- url     : https://prove2.me/theorems/fe5336b7-384f-4e4f-be99-c4592e04519f
-- title:
--   Prof: sum pw le
-- statement:
--   The compared members of a layer, summed over the pairs of nodes, are at most k − 1 times the
--   members of the layer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L260-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L260-L284

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.sum_pw_le {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (i : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, pw g n Ls P a' a i ≤ (k - 1) * (layP Ls P i).card := by sorry
