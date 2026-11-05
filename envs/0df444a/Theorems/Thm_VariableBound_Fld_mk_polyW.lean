-- Prove2me | Theorems.Thm_VariableBound_Fld_mk_polyW
-- name    : VariableBound.Fld.mk_polyW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:18.660199+00:00
-- url     : https://prove2.me/theorems/73e5a0fc-daad-4108-a795-eeed82f34032
-- title:
--   Fld: mk poly W
-- statement:
--   The residue of the polynomial of the word w is the residue that w stands for.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L105-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L105-L106

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

theorem VariableBound.Fld.mk_polyW (g w : List Bool) : AdjoinRoot.mk (modP g) (polyW w) = decW g w := by sorry
