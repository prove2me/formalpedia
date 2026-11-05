-- Prove2me | Theorems.Thm_SparsificationLemma_sat_first
-- name    : SparsificationLemma.sat_first
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:55:24.435486+00:00
-- url     : https://prove2.me/theorems/df32417a-b1b7-43a4-98e1-8836d592521b
-- title:
--   Sparsification Lemma: sat first
-- statement:
--   b satisfies the first child exactly if it satisfies the node and makes a literal of H true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L81-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L81-L86

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

theorem SparsificationLemma.sat_first (b : ℕ → Bool) (x : CNode) (H : PCl) :
    Sat b (leafF (addP [H] x.1, x.2)) ↔ Sat b (leafF x) ∧ ∃ ω ∈ H, b ω.1 = ω.2 := by sorry
