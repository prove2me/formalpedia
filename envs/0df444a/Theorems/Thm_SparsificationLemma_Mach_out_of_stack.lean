-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_out_of_stack
-- name    : SparsificationLemma.Mach.out_of_stack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:49.428005+00:00
-- url     : https://prove2.me/theorems/ea939dc8-a88d-4de8-b3fd-5f526cc40138
-- title:
--   Mach: out of stack
-- statement:
--   What holds of all nodes that are ever on the stack holds of all results: a result was on the
--   stack one round before.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L107-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L107-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_SparsificationLemma_Mach_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {σ : Type} (step : σ → Option (σ × σ))

theorem SparsificationLemma.Mach.out_of_stack (P : σ → Prop) (s : σ) (h : ∀ i, ∀ x ∈ ((round step)^[i] ([s], [])).1, P x) (i : ℕ) :
    ∀ x ∈ ((round step)^[i] ([s], [])).2, P x := by sorry
