-- Prove2me | Theorems.Thm_VariableBound_Fld_bitsW_decW
-- name    : VariableBound.Fld.bitsW_decW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:06.983352+00:00
-- url     : https://prove2.me/theorems/e47c1399-225f-4bcc-b980-f46c2f688653
-- title:
--   Fld: bits W dec W
-- statement:
--   The coordinates of the residue that a word w of s bits stands for are the bits of w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L130-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Quot.lean#L130-L134

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

theorem VariableBound.Fld.bitsW_decW (g w : List Bool) (hw : w.length = g.length) (i : Fin g.length) : bitsW g (decW g w) i = bitR (ZMod 2) (w.getD i.val false) := by sorry
