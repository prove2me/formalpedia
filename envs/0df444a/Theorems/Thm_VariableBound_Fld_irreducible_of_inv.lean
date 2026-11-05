-- Prove2me | Theorems.Thm_VariableBound_Fld_irreducible_of_inv
-- name    : VariableBound.Fld.irreducible_of_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:37:59.742518+00:00
-- url     : https://prove2.me/theorems/97bbad53-5b78-4bed-a22d-3b76c4c88cab
-- title:
--   Fld: irreducible of inv
-- statement:
--   For g of length s ≥ 1: if every residue other than 0 modulo X^s + g has an inverse, then X^s + g
--   is irreducible.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L181-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L181-L187

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

theorem VariableBound.Fld.irreducible_of_inv (g : List Bool) (hg : 1 ≤ g.length) (h : ∀ z : FW g, z ≠ 0 → ∃ z', z * z' = 1) : Irreducible (modP g) := by sorry
