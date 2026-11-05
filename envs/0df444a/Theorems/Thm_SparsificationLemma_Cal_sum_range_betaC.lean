-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_sum_range_betaC
-- name    : SparsificationLemma.Cal.sum_range_betaC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:24:00.072489+00:00
-- url     : https://prove2.me/theorems/18b1efb9-4f85-455d-bbdb-eff44802cc75
-- title:
--   Cal: sum range beta C
-- statement:
--   β₀ + β₁ + … + β_{k−1} = β₁ + … + β_{k−1}, for k ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L111-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Beta.lean#L111-L112

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

theorem SparsificationLemma.Cal.sum_range_betaC (α : ℕ) {k : ℕ} (hk : 1 ≤ k) : ∑ c ∈ range k, betaC α c = ∑ c ∈ Ico 1 k, betaC α c := by sorry
