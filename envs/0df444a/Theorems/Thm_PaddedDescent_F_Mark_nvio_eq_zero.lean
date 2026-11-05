-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_nvio_eq_zero
-- name    : PaddedDescent.F.Mark.nvio_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:26.643208+00:00
-- url     : https://prove2.me/theorems/75c16597-e095-4f98-bda3-baca9ecbd18a
-- title:
--   Mark: nvio eq zero
-- statement:
--   σ violates no clause of L exactly if every clause of L has a true literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L55-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkSums
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog

theorem PaddedDescent.F.Mark.nvio_eq_zero {σ : ℕ → Bool} {L : Fml} : nvio σ L = 0 ↔ ∀ C ∈ L, ∃ l ∈ C, σ l.1 = l.2 := by sorry
