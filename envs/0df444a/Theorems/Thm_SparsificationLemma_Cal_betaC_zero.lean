-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_betaC_zero
-- name    : SparsificationLemma.Cal.betaC_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:36:50.094643+00:00
-- url     : https://prove2.me/theorems/c2eddf1d-7965-4061-a5e7-610059c58f2b
-- title:
--   Cal: beta C zero
-- statement:
--   β₀ = 0, the convention of Cal/Defs.lean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L37-L37

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

theorem SparsificationLemma.Cal.betaC_zero (α : ℕ) : betaC α 0 = 0 := by sorry
