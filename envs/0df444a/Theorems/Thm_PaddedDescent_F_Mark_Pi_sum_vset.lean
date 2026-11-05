-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Pi_sum_vset
-- name    : PaddedDescent.F.Mark.Pi.sum_vset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:20.406204+00:00
-- url     : https://prove2.me/theorems/aa438d77-e42c-40c9-b2d7-fb05140b4e89
-- title:
--   Pi: sum vset
-- statement:
--   The sum, over the sets P of violated clauses with at most w clauses in every layer, of the sign
--   of P is the product of the cut-off sums of the layers: unsigned for the
--   first layer, signed for the others.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L264-L274
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkPi.lean#L264-L274

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkPi
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Pi
open Finset Groundwork Groundwork.Prog
variable {ι : Type*} [DecidableEq ι]

theorem PaddedDescent.F.Mark.Pi.sum_vset (σ : ℕ → Bool) (w : ℕ) (Ls : List Fml) :
    ∑ P ∈ (vset σ Ls).powerset.filter (fun P => ∀ i < Ls.length, (layP Ls P i).card ≤ w), sgnP Ls P =
      Tpl w (nvio σ (Ls.headD [])) * (Ls.tail.map fun L => Tsg w (nvio σ L)).prod := by sorry
