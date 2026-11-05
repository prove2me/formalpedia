-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_U_markN_le
-- name    : PaddedDescent.F.Mark.Size.U_markN_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:28.2293+00:00
-- url     : https://prove2.me/theorems/0e083723-5026-4a2f-be2f-dd707dfef510
-- title:
--   Size: U mark N le
-- statement:
--   A bound on the shared bits of the network of an admissible profile whose clauses have at most k
--   literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L436-L474
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L436-L474

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

theorem PaddedDescent.F.Mark.Size.U_markN_le {gu nu βu bu : U} {w y k : ℕ} (h : adm k gu.length nu.length w Ls y = true) (hk : ∀ L ∈ Ls, ∀ C ∈ L, C.length ≤ k) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U ≤
      2 * ∑ i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length)) := by sorry
