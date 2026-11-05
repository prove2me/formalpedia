-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_trunc_of_good
-- name    : PaddedDescent.F.Mark.trunc_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:40:09.437204+00:00
-- url     : https://prove2.me/theorems/643f11df-d862-493d-a04e-377d1e5f1a6a
-- title:
--   Mark: trunc of good
-- statement:
--   One evaluation on good layers: the sum of 2^(number of violated clauses of the first layer) over
--   the assignments that satisfy the other layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L80-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L80-L88

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

theorem PaddedDescent.F.Mark.trunc_of_good {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : Good n w (Λ :: rest)) :
    trunc n w (Λ :: rest) = ∑ σ : Fin n → Bool, if ∀ L ∈ rest, nvio (ext σ) L = 0 then (2 : ℤ) ^ nvio (ext σ) Λ else 0 := by sorry
