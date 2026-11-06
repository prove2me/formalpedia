-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_gen
-- name    : SparsificationLemma.Cal.gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:08:23.075602+00:00
-- url     : https://prove2.me/theorems/b98bb1c5-b03b-49f1-b580-c19a496894d4
-- title:
--   Cal: gen
-- statement:
--   The general theorem for Calabro's thresholds, with τ = α and D = (β₁ + … + β_{k−1})·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Facts.lean#L40-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Facts.lean#L40-L45

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

theorem SparsificationLemma.Cal.gen {α k n : ℕ} {ψ : PFml} (hα : 1 ≤ α) (hk : 1 ≤ k) (hψ : IsKCNF k n ψ) :
    (∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, stepC (thetaC α) k x = none) ∧
    (outputs (thetaC α) k (depthC α k n) ψ).length ≤ ∑ j ∈ range ((k - 1) * n / α + 1), (depthC α k n).choose j ∧
    (∀ Φ ∈ outputs (thetaC α) k (depthC α k n) ψ, IsKCNF k n Φ ∧ ∀ v, occN Φ v ≤ 2 * (∑ j ∈ range k, thetaC α j) + 2) ∧
    ∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, x.1.length ≤ ψ.length := by sorry
