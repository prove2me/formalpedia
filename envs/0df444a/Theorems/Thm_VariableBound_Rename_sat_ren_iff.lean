-- Prove2me | Theorems.Thm_VariableBound_Rename_sat_ren_iff
-- name    : VariableBound.Rename.sat_ren_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:57.188329+00:00
-- url     : https://prove2.me/theorems/42633016-2df4-4fe4-9587-2ad2ff3003a8
-- title:
--   Rename: sat ren iff
-- statement:
--   An assignment a of x₀ … x_(n−1) satisfies the renamed formula if and only if the assignment «a
--   at the new name» of the variables that occur satisfies φ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L148-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Math.lean#L148-L160

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
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)
variable {N : ℕ} (φ : CNF N)

theorem VariableBound.Rename.sat_ren_iff (a : Fin (numOcc φ) → Bool) :
    (∀ C ∈ ren φ, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ C ∈ φ, ∃ l ∈ C, ∃ h : Occurs φ l.1, a (pos φ ⟨l.1, h⟩) = l.2 := by sorry
