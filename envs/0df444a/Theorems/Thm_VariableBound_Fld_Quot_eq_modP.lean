-- Prove2me | Theorems.Thm_VariableBound_Fld_Quot_eq_modP
-- name    : VariableBound.Fld.Quot.eq_modP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:37:41.352495+00:00
-- url     : https://prove2.me/theorems/f47c50f6-1192-49f4-844e-b5db90a457e8
-- title:
--   Quot: eq mod P
-- statement:
--   A monic polynomial of degree s over the field with two elements is X^s + g for the word g of its
--   s lower coefficients.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L161-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L161-L170

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

theorem VariableBound.Fld.Quot.eq_modP (f : (ZMod 2)[X]) (hf : f.Monic) : modP (List.ofFn fun i : Fin f.natDegree => decide (f.coeff i = 1)) = f := by sorry
