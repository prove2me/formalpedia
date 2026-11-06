-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_log_le_mul_log_two
-- name    : SparsificationLemma.Geo.log_le_mul_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:02:11.234252+00:00
-- url     : https://prove2.me/theorems/fcc496f7-b596-4b53-8efa-a2bf50de9f6c
-- title:
--   Geo: log le mul log two
-- statement:
--   ln y ≤ y·ln 2 for y > 0, that is log₂ y ≤ y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Eps.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Eps.lean#L30-L35

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

theorem SparsificationLemma.Geo.log_le_mul_log_two {y : ℝ} (hy : 0 < y) : Real.log y ≤ y * Real.log 2 := by sorry
