-- Prove2me | Theorems.Thm_VariableBound_Fld_Quot_getD_ofFn
-- name    : VariableBound.Fld.Quot.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:14.180212+00:00
-- url     : https://prove2.me/theorems/50d9e2c2-571a-41b4-a51e-1813dab17f07
-- title:
--   Quot: get D of Fn
-- statement:
--   The i-th entry of the word of the bits x_0, …, x_(n−1) is x_i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L56-L57

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

theorem VariableBound.Fld.Quot.getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by sorry
