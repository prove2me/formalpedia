-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_iff
-- name    : PaddedDescent.F.Mark.Prof.adm_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:13.915274+00:00
-- url     : https://prove2.me/theorems/18956feb-ea1f-4193-9327-cdad9eec94f5
-- title:
--   Prof: adm iff
-- statement:
--   What `adm` says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L296-L309
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L296-L309

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

theorem PaddedDescent.F.Mark.Prof.adm_iff (k g n w : ℕ) (Ls : List Fml) (y : ℕ) : adm k g n w Ls y = true ↔ ∀ i < Ls.length,
    ∑ a ∈ range g, mu g Ls y a a i ≤ w ∧ ∑ a ∈ range g, ∑ a' ∈ range a, mu g Ls y a' a i ≤ (k - 1) * w ∧
    ∀ a < g, ∀ a' < g, (a' < a → digit (cls Ls).length y ((a * g + a') * Ls.length + i) = 0) ∧
      (a < a' → mu g Ls y a a' i ≤ (tst g n Ls a a' i).length) := by sorry
