-- Prove2me | Theorems.Thm_VariableBound_Rename_map_back
-- name    : VariableBound.Rename.map_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:07.790996+00:00
-- url     : https://prove2.me/theorems/831e79eb-29c6-4159-bc9f-e4be14f4423d
-- title:
--   Rename: map back
-- statement:
--   Putting the old names back: the inverse of the renaming on clauses all of whose variables are in
--   the list L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L116-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L116-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_VariableBound_Paper_Rename_Math
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)

theorem VariableBound.Rename.map_back {L : List ℕ} {C : List (ℕ × Bool)} (h : ∀ l ∈ C, l.1 ∈ L) :
    (C.map fun l => (L.idxOf l.1, l.2)).map (fun l => (L.getD l.1 0, l.2)) = C := by sorry
