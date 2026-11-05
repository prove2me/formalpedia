-- Prove2me | Theorems.Thm_StepSparsify_leaves_eq_of_le
-- name    : StepSparsify.leaves_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:08:56.393294+00:00
-- url     : https://prove2.me/theorems/91d5bf1a-8799-47d8-9634-ac1c9b8e1d87
-- title:
--   Step Sparsify: leaves eq of le
-- statement:
--   If the procedure has stopped at every node that is listed when the paths are cut after D₀ steps,
--   then cutting them after D ≥ D₀ steps gives the same list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L34-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L34-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepSparsify_CalLeaves
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma

theorem StepSparsify.leaves_eq_of_le {σ : Type*} (step : σ → Option (σ × σ)) (D₀ : ℕ) : ∀ (D : ℕ) (r : σ), D₀ ≤ D →
    (∀ x ∈ leaves step D₀ r, step x = none) → leaves step D r = leaves step D₀ r := by sorry
