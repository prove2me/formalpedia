-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_card_links_le
-- name    : PaddedDescent.F.Mark.Prof.card_links_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:54:35.13681+00:00
-- url     : https://prove2.me/theorems/807642e7-565e-4e4b-af21-2468cd765d62
-- title:
--   Prof: card links le
-- statement:
--   A clause has at most k − 1 links.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L197-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L197-L232

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.card_links_le {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    ((range g ×ˢ range g).filter fun p => linkB g n Ls e p.1 p.2 = true).card ≤ k - 1 := by sorry
