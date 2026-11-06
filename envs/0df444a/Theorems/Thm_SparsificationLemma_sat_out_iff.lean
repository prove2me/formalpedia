-- Prove2me | Theorems.Thm_SparsificationLemma_sat_out_iff
-- name    : SparsificationLemma.sat_out_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:14.290516+00:00
-- url     : https://prove2.me/theorems/4153570f-52d3-4537-b18f-92a3724a9e4e
-- title:
--   Sparsification Lemma: sat out iff
-- statement:
--   If every side clause has one literal, the output `out x` has the satisfying assignments of
--   `leafF x`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L71-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L71-L72

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

theorem SparsificationLemma.sat_out_iff (b : ℕ → Bool) {x : CNode} (hx : ∀ C ∈ x.2, ∃ l, C = [l]) : Sat b (out x) ↔ Sat b (leafF x) := by sorry
