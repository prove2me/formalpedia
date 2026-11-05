-- Prove2me | Theorems.Thm_VariableBound_Fld_Quot_bitR_inj
-- name    : VariableBound.Fld.Quot.bitR_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:37:28.637006+00:00
-- url     : https://prove2.me/theorems/17e6ba73-1823-4224-9678-f40f7f6b1bc0
-- title:
--   Quot: bit R inj
-- statement:
--   Different bits are different elements of ZMod 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L51-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L51-L53

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

theorem VariableBound.Fld.Quot.bitR_inj {b b' : Bool} (h : bitR (ZMod 2) b = bitR (ZMod 2) b') : b = b' := by sorry
