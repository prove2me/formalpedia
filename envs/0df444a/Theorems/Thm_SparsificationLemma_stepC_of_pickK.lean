-- Prove2me | Theorems.Thm_SparsificationLemma_stepC_of_pickK
-- name    : SparsificationLemma.stepC_of_pickK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:41.859217+00:00
-- url     : https://prove2.me/theorems/800c2c9a-01bf-4e18-a831-77a883c2095e
-- title:
--   Sparsification Lemma: step C of pick K
-- statement:
--   The two children of a node at which the rule picks H, with P the list of the E ∖ H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L77-L78

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount

theorem SparsificationLemma.stepC_of_pickK {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {P : PFml} (hp : pickK θ k x.1 = some (H, P)) :
    stepC θ k x = some ((addP [H] x.1, x.2), (addP P x.1, negU H ++ x.2)) := by sorry
