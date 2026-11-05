-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_works_of_cube
-- name    : SparsificationLemma.Geo.works_of_cube
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:16.880854+00:00
-- url     : https://prove2.me/theorems/ffa71839-0228-4eae-af51-7e09aee329d7
-- title:
--   Geo: works of cube
-- statement:
--   The inequality of `StTauE` between real numbers: (k/T)·log₂(e·T·T^(2k)) ≤ ε, if X = 8k/ε, k ≥ 1,
--   ε ∈ (0,1] and X³ ≤ T ≤ (9X/8)³.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Eps.lean#L39-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Eps.lean#L39-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Geo_Eps
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open UniformInK

theorem SparsificationLemma.Geo.works_of_cube {k : ℕ} {ε X T : ℝ} (hk : 1 ≤ (k : ℝ)) (h0 : 0 < ε) (h1 : ε ≤ 1) (hX : (k : ℝ) = ε * X / 8)
    (hlo : X ^ 3 ≤ T) (hhi : T ≤ (9 * X / 8) ^ 3) :
    ((k : ℝ) / T) * Real.logb 2 (Real.exp 1 * T * T ^ (2 * k)) ≤ ε := by sorry
