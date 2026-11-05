-- Prove2me | Theorems.Thm_VariableBound_Fld_exists_irreducible_modP
-- name    : VariableBound.Fld.exists_irreducible_modP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:38:02.018989+00:00
-- url     : https://prove2.me/theorems/12cded31-546b-4530-9aac-02ed98dca201
-- title:
--   Fld: exists irreducible mod P
-- statement:
--   For every s ≥ 1 there is a word g of s bits such that X^s + g is irreducible.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L173-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L173-L177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Alg
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Definitions.Def_VariableBound_Field_Quot
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
open VariableBound.Fld.Quot

theorem VariableBound.Fld.exists_irreducible_modP (s : ℕ) (hs : 1 ≤ s) : ∃ g : List Bool, g.length = s ∧ Irreducible (modP g) := by sorry
