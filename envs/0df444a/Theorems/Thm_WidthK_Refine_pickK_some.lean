-- Prove2me | Theorems.Thm_WidthK_Refine_pickK_some
-- name    : WidthK.Refine.pickK_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:28.672367+00:00
-- url     : https://prove2.me/theorems/18cdb899-58bb-4173-ba4c-ba74eaa52762
-- title:
--   Refine: pick K some
-- statement:
--   An answer of `pickK` is the answer of `tryP` at some pair, and `tryP` has no answer at the pairs
--   that come before it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L219-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L219-L231

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.pickK_some {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {HP : PCl × PFml} (h : pickK θ k s = some HP) :
    ∃ jh ∈ pairsK k, tryP θ k s jh = some HP ∧ ∀ x ∈ pairsK k, Before x jh → tryP θ k s x = none := by sorry
