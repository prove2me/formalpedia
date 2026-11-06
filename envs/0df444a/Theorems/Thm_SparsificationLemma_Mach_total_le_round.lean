-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_total_le_round
-- name    : SparsificationLemma.Mach.total_le_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:49.197454+00:00
-- url     : https://prove2.me/theorems/eee0980a-75be-4750-92fe-d0b293853faf
-- title:
--   Mach: total le round
-- statement:
--   A round does not decrease the number of nodes on the stack and in the list of results together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L85-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Walk.lean#L85-L89

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

theorem SparsificationLemma.Mach.total_le_round (st : List σ × List σ) : st.1.length + st.2.length ≤ (round step st).1.length + (round step st).2.length := by sorry
