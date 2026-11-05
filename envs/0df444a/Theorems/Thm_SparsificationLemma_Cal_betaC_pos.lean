-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_betaC_pos
-- name    : SparsificationLemma.Cal.betaC_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:55.999192+00:00
-- url     : https://prove2.me/theorems/9eef2fdd-f927-473e-9c43-a9bb5c7bb3eb
-- title:
--   Cal: beta C pos
-- statement:
--   β_c ≥ 1 for c ≥ 1, if α ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L81-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L81-L83

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

theorem SparsificationLemma.Cal.betaC_pos {α : ℕ} (hα : 1 ≤ α) (c : ℕ) : 0 < betaC α (c + 1) := by sorry
