-- Prove2me | Theorems.Thm_SparsificationLemma_countP_outputs
-- name    : SparsificationLemma.countP_outputs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:05.921374+00:00
-- url     : https://prove2.me/theorems/86696c19-2511-43eb-9a23-d95acd10225f
-- title:
--   Sparsification Lemma: count P outputs
-- statement:
--   The number of outputs (positions of the list) that b satisfies is 1 if b satisfies ψ, and 0
--   otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L149-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L149-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto
import Definitions.Def_SparsificationLemma_One
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount

theorem SparsificationLemma.countP_outputs (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) (b : ℕ → Bool) :
    (outputs θ k D ψ).countP (fun Ψ => decide (Sat b Ψ)) = if Sat b ψ then 1 else 0 := by sorry
