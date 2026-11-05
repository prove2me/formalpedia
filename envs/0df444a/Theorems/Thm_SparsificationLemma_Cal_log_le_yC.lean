-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_log_le_yC
-- name    : SparsificationLemma.Cal.log_le_yC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:50.524346+00:00
-- url     : https://prove2.me/theorems/0e8fdcfe-251a-4079-a84a-17cfad35a71e
-- title:
--   Cal: log le y C
-- statement:
--   ((k−1)/α)·log₂(e·α·L) ≤ y for L = 4·(32α)^(k−2), α ≥ 1 and k ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Facts.lean#L51-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Facts.lean#L51-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Facts
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

theorem SparsificationLemma.Cal.log_le_yC {α k : ℕ} (hα : 1 ≤ α) (hk : 2 ≤ k) :
    (((k - 1 : ℕ) : ℝ) / (α : ℝ)) * Real.logb 2 (Real.exp 1 * (α : ℝ) * ((4 * (32 * α) ^ (k - 2) : ℕ) : ℝ)) ≤ yC k α := by sorry
