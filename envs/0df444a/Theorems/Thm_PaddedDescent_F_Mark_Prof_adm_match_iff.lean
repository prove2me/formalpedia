-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_match_iff
-- name    : PaddedDescent.F.Mark.Prof.adm_match_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:46.415851+00:00
-- url     : https://prove2.me/theorems/ad5f33d8-e87d-4c08-9bf5-5ee7e02c5a5e
-- title:
--   Prof: adm match iff
-- statement:
--   y is an admissible profile of P exactly if the caps hold for P and y has the digits of P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L336-L373
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L336-L373

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

theorem PaddedDescent.F.Mark.Prof.adm_match_iff {k g n : ℕ} (w : ℕ) {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length)
    (y : ℕ) : (adm k g n w Ls y = true ∧ Match g n Ls y P) ↔
      ((∀ i < Ls.length, (layP Ls P i).card ≤ w) ∧ ∀ q < g * g * Ls.length, digit (cls Ls).length y q = tgt g n Ls P q) := by sorry
