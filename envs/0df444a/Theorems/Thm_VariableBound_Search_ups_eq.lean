-- Prove2me | Theorems.Thm_VariableBound_Search_ups_eq
-- name    : VariableBound.Search.ups_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:40:35.706408+00:00
-- url     : https://prove2.me/theorems/bdd62284-6255-4bef-9887-03b13b396eae
-- title:
--   Search: ups eq
-- statement:
--   Υ(𝓛) is `upsNum` over the denominator, for n̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L95-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Correct.lean#L95-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset

theorem VariableBound.Search.ups_eq {X : Type} [Fintype X] (m : ℕ) (V : X → Finset (Fin m)) (nb β rb tb : ℕ) (L : List (List ℕ)) (hnb : 1 ≤ nb) :
    Ups V nb β rb tb (chksD m L) = (upsNum m nb β rb tb (Xsum V nb (chksD m L)) L : ℚ) / den nb β rb tb L.length := by sorry
