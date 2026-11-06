-- Prove2me | Theorems.Thm_SparsificationLemma_sideU_append_taut
-- name    : SparsificationLemma.sideU_append_taut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:55.900149+00:00
-- url     : https://prove2.me/theorems/a5bd63ca-3481-4f69-bf30-524b54cfd078
-- title:
--   Sparsification Lemma: side U append taut
-- statement:
--   The clauses xᵢ ∨ ¬xᵢ do not reach the output: they have two literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L42-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Side.lean#L42-L47

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

theorem SparsificationLemma.sideU_append_taut (X : PFml) (n : ℕ) : sideU (X ++ taut n) = sideU X := by sorry
