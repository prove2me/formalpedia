-- Prove2me | Theorems.Thm_SparsificationLemma_sat_second
-- name    : SparsificationLemma.sat_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:05.482902+00:00
-- url     : https://prove2.me/theorems/9f9696be-42ff-43e9-a0ab-8056ec9978fd
-- title:
--   Sparsification Lemma: sat second
-- statement:
--   b satisfies the second child exactly if it satisfies the node and makes no literal of H true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L89-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L89-L94

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

theorem SparsificationLemma.sat_second {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {P : PFml} (hp : pickK θ k x.1 = some (H, P)) (b : ℕ → Bool) :
    Sat b (leafF (addP P x.1, negU H ++ x.2)) ↔ Sat b (leafF x) ∧ ¬ ∃ ω ∈ H, b ω.1 = ω.2 := by sorry
