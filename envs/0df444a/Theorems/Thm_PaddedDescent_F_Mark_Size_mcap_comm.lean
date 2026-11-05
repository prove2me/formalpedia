-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_mcap_comm
-- name    : PaddedDescent.F.Mark.Size.mcap_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:54.269486+00:00
-- url     : https://prove2.me/theorems/34ae2cc7-29cd-411c-94e9-c79c228c0416
-- title:
--   Size: mcap comm
-- statement:
--   The capacities are symmetric.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L274-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L274-L275

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.mcap_comm (β b y a a' : ℕ) : mcap g n β b Ls y a a' = mcap g n β b Ls y a' a := by sorry
