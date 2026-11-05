-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sized_markN
-- name    : PaddedDescent.F.Mark.Size.sized_markN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:27.914244+00:00
-- url     : https://prove2.me/theorems/50e09f10-7a6d-459a-b073-a7762efdb183
-- title:
--   Size: sized mark N
-- statement:
--   The network of an admissible profile has size P, with entries 0, 1, −1, if at every node P
--   bounds qv plus the number of touching clauses, and
--   2(2 + β) times that number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L346-L387
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L346-L387

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

theorem PaddedDescent.F.Mark.Size.sized_markN {gu nu βu bu : U} {k w y P : ℕ} (h0 : 0 < bu.length) (h : adm k gu.length nu.length w Ls y = true)
    (hP : ∀ a < gu.length, qv gu.length nu.length + (tch gu.length nu.length Ls a).length ≤ P ∧
      2 * (2 + βu.length) * (tch gu.length nu.length Ls a).length ≤ P) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).Sized P 0 := by sorry
