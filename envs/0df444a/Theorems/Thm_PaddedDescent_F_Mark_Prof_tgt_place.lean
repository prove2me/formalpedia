-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_place
-- name    : PaddedDescent.F.Mark.Prof.tgt_place
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:14.451226+00:00
-- url     : https://prove2.me/theorems/f08ad9b4-c10e-41ee-a233-5e2dd1b2c973
-- title:
--   Prof: tgt place
-- statement:
--   The digit of P at the place (A·g + A')·R + i, where R is the number of layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L318-L323
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L318-L323

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

theorem PaddedDescent.F.Mark.Prof.tgt_place {g n : ℕ} {Ls : List Fml} (P : Finset ℕ) {A A' i : ℕ} (hA' : A' < g) (hi : i < Ls.length) :
    tgt g n Ls P ((A * g + A') * Ls.length + i) =
      if A' < A then 0 else if A = A' then oc g n Ls P A i else pw g n Ls P A A' i := by sorry
