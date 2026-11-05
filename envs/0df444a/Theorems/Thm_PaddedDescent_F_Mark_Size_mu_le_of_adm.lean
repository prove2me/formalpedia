-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_mu_le_of_adm
-- name    : PaddedDescent.F.Mark.Size.mu_le_of_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:16.902163+00:00
-- url     : https://prove2.me/theorems/dab6d38b-4c56-4cf0-8716-682d90c84c3d
-- title:
--   Size: mu le of adm
-- statement:
--   An admissible profile prescribes for two different nodes at most as many set marks as they
--   compare.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L302-L306
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L302-L306

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.mu_le_of_adm {k w y : ℕ} (h : adm k g n w Ls y = true) {a a' i : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') (hi : i < Ls.length) :
    mu g Ls y a a' i ≤ (tst g n Ls a a' i).length := by sorry
