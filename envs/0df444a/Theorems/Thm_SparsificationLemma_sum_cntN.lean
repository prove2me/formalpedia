-- Prove2me | Theorems.Thm_SparsificationLemma_sum_cntN
-- name    : SparsificationLemma.sum_cntN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:50.83279+00:00
-- url     : https://prove2.me/theorems/4b8f456f-68d4-4f98-907e-bc7368a1adbb
-- title:
--   Sparsification Lemma: sum cnt N
-- statement:
--   The sum of the counts of the formulas of Φ is the sum, over the assignments, of the number of
--   positions of Φ that the assignment satisfies.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L170-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L170-L173

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
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount

theorem SparsificationLemma.sum_cntN (n : ℕ) (Φ : List PFml) : (Φ.map (cntN n)).sum = ∑ a : Fin n → Bool, Φ.countP fun Ψ => decide (Sat (ext a) Ψ) := by sorry
