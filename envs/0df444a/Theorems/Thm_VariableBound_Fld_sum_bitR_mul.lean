-- Prove2me | Theorems.Thm_VariableBound_Fld_sum_bitR_mul
-- name    : VariableBound.Fld.sum_bitR_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:07.063238+00:00
-- url     : https://prove2.me/theorems/04d5124f-7c1d-4135-9bbc-cd511fbbc501
-- title:
--   Fld: sum bit R mul
-- statement:
--   The sum over the places of the products of the bits of two words of n bits is, modulo 2, the
--   number of places where both bits are set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L49-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L49-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial

theorem VariableBound.Fld.sum_bitR_mul (n : ℕ) : ∀ x y : List Bool, x.length = n → y.length = n →
    ∑ i : Fin n, bitR (ZMod 2) (x.getD i.val false) * bitR (ZMod 2) (y.getD i.val false) = (((x.zip y).countP fun p => p.1 && p.2 : ℕ) : ZMod 2) := by sorry
