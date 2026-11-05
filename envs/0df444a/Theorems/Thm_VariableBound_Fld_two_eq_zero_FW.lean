-- Prove2me | Theorems.Thm_VariableBound_Fld_two_eq_zero_FW
-- name    : VariableBound.Fld.two_eq_zero_FW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:37.998823+00:00
-- url     : https://prove2.me/theorems/403ce2af-ba13-48b9-88fb-b13cc41d1e94
-- title:
--   Fld: two eq zero FW
-- statement:
--   2 = 0 in the ring of residues.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L100-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L100-L102

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

theorem VariableBound.Fld.two_eq_zero_FW (g : List Bool) : (2 : FW g) = 0 := by sorry
