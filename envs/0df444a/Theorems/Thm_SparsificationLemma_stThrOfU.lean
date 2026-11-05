-- Prove2me | Theorems.Thm_SparsificationLemma_stThrOfU
-- name    : SparsificationLemma.stThrOfU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:22.447272+00:00
-- url     : https://prove2.me/theorems/3c754c3a-9628-4222-8aa7-ac3d10060536
-- title:
--   Sparsification Lemma: st Thr Of U
-- statement:
--   The conditions `ThrU` together with 2 ≤ β 1 imply the conditions `ThrC`: `ThrC.step` asks at the
--   sizes i ≥ 2 what `ThrU.step` asks at all sizes i ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Bound.lean#L35-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_UniformInK_Spars_Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK UniformInK

theorem SparsificationLemma.stThrOfU : StThrOfU := by sorry
