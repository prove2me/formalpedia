-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_adm_match_iff
-- name    : VariableBound.Net.Prof.adm_match_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:45:27.486579+00:00
-- url     : https://prove2.me/theorems/1e74f6b1-5862-4dc8-a782-491b3af60aa4
-- title:
--   Prof: adm match iff
-- statement:
--   If 0 < g, the data are well formed and P is a set of positions of objects: y is an admissible
--   profile to which P belongs iff |Π₀| = n̄ + 1 (for F: ≤ n̄), Σ_j |Π_j| ≤ M, and y has the digits of
--   P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L322-L357
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L322-L357

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_match_iff
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.adm_match_iff {k g n : ℕ} (nb M : ℕ) {D : Dat} (fl : Bool) (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length)
    (y : ℕ) : (admD k g n nb M D fl y = true ∧ Match g n D y P) ↔
      (Lim nb M D fl P ∧ ∀ q < g * g * 2, digit (objs D).length y q = tgt g n D P q) := by sorry
