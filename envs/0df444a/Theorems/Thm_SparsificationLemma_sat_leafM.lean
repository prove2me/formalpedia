-- Prove2me | Theorems.Thm_SparsificationLemma_sat_leafM
-- name    : SparsificationLemma.sat_leafM
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:04.42963+00:00
-- url     : https://prove2.me/theorems/a7805a88-60bb-4b6e-adeb-a20e3c541bb1
-- title:
--   Sparsification Lemma: sat leaf M
-- statement:
--   If every side clause has one literal, `leafM x` has the satisfying assignments of `leafF x`: it
--   only lacks the repetitions in the side list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L62-L63

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

theorem SparsificationLemma.sat_leafM (b : ℕ → Bool) {x : CNode} (hx : ∀ C ∈ x.2, ∃ l, C = [l]) : Sat b (leafM x) ↔ Sat b (leafF x) := by sorry
