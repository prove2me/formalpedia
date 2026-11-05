-- Prove2me | Theorems.Thm_VariableBound_Fld_Quot_bitR_decide
-- name    : VariableBound.Fld.Quot.bitR_decide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:16.818927+00:00
-- url     : https://prove2.me/theorems/f23ba65b-9425-424d-98a0-96ce86df74f9
-- title:
--   Quot: bit R decide
-- statement:
--   In ZMod 2, c is the bit «c = 1».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L46-L48

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

theorem VariableBound.Fld.Quot.bitR_decide (c : ZMod 2) : bitR (ZMod 2) (decide (c = 1)) = c := by sorry
