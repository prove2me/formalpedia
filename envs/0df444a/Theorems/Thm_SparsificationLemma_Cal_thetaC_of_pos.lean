-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_thetaC_of_pos
-- name    : SparsificationLemma.Cal.thetaC_of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:24:18.719392+00:00
-- url     : https://prove2.me/theorems/66e3397c-1b0b-43a6-961c-1b47c5a08f7b
-- title:
--   Cal: theta C of pos
-- statement:
--   θ_c = α·β_c for c ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L40-L42

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

theorem SparsificationLemma.Cal.thetaC_of_pos (α : ℕ) {c : ℕ} (hc : 1 ≤ c) : thetaC α c = α * betaC α c := by sorry
