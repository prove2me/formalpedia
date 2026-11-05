-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_total_le_leaves
-- name    : SparsificationLemma.Mach.total_le_leaves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:55.46904+00:00
-- url     : https://prove2.me/theorems/11f112ed-27be-4292-9f0a-2e3f26bc1c1a
-- title:
--   Mach: total le leaves
-- statement:
--   After any number of rounds, the stack and the list of results together have at most as many
--   nodes as there are leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L99-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L99-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_SparsificationLemma_Mach_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg
variable {σ : Type} (step : σ → Option (σ × σ))

theorem SparsificationLemma.Mach.total_le_leaves (d : ℕ) (s : σ) (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length + ((round step)^[i] ([s], [])).2.length ≤ (leaves step d s).length := by sorry
