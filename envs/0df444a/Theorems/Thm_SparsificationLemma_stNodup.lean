-- Prove2me | Theorems.Thm_SparsificationLemma_stNodup
-- name    : SparsificationLemma.stNodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:07:59.601711+00:00
-- url     : https://prove2.me/theorems/a34dbcdd-4c1f-404c-aa08-460a6a49d9d9
-- title:
--   Sparsification Lemma: st Nodup
-- statement:
--   No output has a clause twice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L58-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L58-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_SparsifyList
import Definitions.Def_SparsificationLemma_Side
set_option autoImplicit false
section
section
open SparsificationLemma
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate

theorem SparsificationLemma.stNodup : StNodup := by sorry
