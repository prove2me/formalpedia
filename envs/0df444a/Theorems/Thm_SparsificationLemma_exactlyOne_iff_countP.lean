-- Prove2me | Theorems.Thm_SparsificationLemma_exactlyOne_iff_countP
-- name    : SparsificationLemma.exactlyOne_iff_countP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:06:34.640791+00:00
-- url     : https://prove2.me/theorems/ffe6fa09-af28-4d5a-90d4-1697ca57495e
-- title:
--   Sparsification Lemma: exactly One iff count P
-- statement:
--   `ExactlyOne b ψ Φ` says that the number of positions of Φ that b satisfies is 1 if b satisfies
--   ψ, and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L109-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L109-L117

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

theorem SparsificationLemma.exactlyOne_iff_countP (b : ℕ → Bool) (ψ : PFml) (Φ : List PFml) :
    ExactlyOne b ψ Φ ↔ Φ.countP (fun Ψ => decide (Sat b Ψ)) = if Sat b ψ then 1 else 0 := by sorry
