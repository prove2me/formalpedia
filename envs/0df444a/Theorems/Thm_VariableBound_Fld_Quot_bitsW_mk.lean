-- Prove2me | Theorems.Thm_VariableBound_Fld_Quot_bitsW_mk
-- name    : VariableBound.Fld.Quot.bitsW_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:37:34.537198+00:00
-- url     : https://prove2.me/theorems/6898a931-645e-41d6-aef8-5711479982f1
-- title:
--   Quot: bits W mk
-- statement:
--   The i-th coordinate of the residue of a polynomial p is the coefficient of X^i in the remainder
--   of p modulo X^s + g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L124-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L124-L127

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

theorem VariableBound.Fld.Quot.bitsW_mk (g : List Bool) (p : (ZMod 2)[X]) (i : Fin g.length) : bitsW g (AdjoinRoot.mk (modP g) p) i = (p %ₘ modP g).coeff i.val := by sorry
