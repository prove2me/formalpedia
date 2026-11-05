-- Prove2me | Theorems.Thm_VariableBound_Fld_decW_surj
-- name    : VariableBound.Fld.decW_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:44.277658+00:00
-- url     : https://prove2.me/theorems/5fbcb94d-a9bb-4297-b93d-2be6c0aa5375
-- title:
--   Fld: dec W surj
-- statement:
--   Every residue is the one that some word of s bits stands for.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L137-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L137-L139

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

theorem VariableBound.Fld.decW_surj (g : List Bool) (z : FW g) : ∃ w : List Bool, w.length = g.length ∧ decW g w = z := by sorry
