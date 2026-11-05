-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_betaC_one
-- name    : SparsificationLemma.Cal.betaC_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:25:37.149558+00:00
-- url     : https://prove2.me/theorems/1a6c701b-da21-4d9f-bfae-3a0f66bcb115
-- title:
--   Cal: beta C one
-- statement:
--   β₁ = 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L34-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset

theorem SparsificationLemma.Cal.betaC_one (α : ℕ) : betaC α 1 = 2 := by sorry
