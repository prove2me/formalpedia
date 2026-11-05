-- Prove2me | Theorems.Thm_VariableBound_Fld_decW_inj
-- name    : VariableBound.Fld.decW_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:24.054448+00:00
-- url     : https://prove2.me/theorems/464920f6-01d7-4580-a1c8-bf301ae6629b
-- title:
--   Fld: dec W inj
-- statement:
--   Two words of s bits that stand for the same residue are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L142-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L142-L148

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

theorem VariableBound.Fld.decW_inj (g : List Bool) {w w' : List Bool} (hw : w.length = g.length) (hw' : w'.length = g.length) (h : decW g w = decW g w') : w = w' := by sorry
