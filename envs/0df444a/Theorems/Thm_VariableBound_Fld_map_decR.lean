-- Prove2me | Theorems.Thm_VariableBound_Fld_map_decR
-- name    : VariableBound.Fld.map_decR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:37:30.221235+00:00
-- url     : https://prove2.me/theorems/da20606f-bf60-42c1-be1c-d5c947bb7b6f
-- title:
--   Fld: map dec R
-- statement:
--   A homomorphism φ of rings maps b_0 + b_1·r + … to b_0 + b_1·φ(r) + ….
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L78-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L78-L81

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

theorem VariableBound.Fld.map_decR {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R) (w : List Bool) : φ (decR r w) = decR (φ r) w := by sorry
