-- Prove2me | Theorems.Thm_VariableBound_Fld_ipW_iff
-- name    : VariableBound.Fld.ipW_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:11.842291+00:00
-- url     : https://prove2.me/theorems/8784b158-07a8-435e-979b-2d82eafb4276
-- title:
--   Fld: ip W iff
-- statement:
--   `ipW` is the inner product ⟨·,·⟩ modulo 2 of the proof of Lemma 13, for two words of n bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Field/Family.lean#L66-L68

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

theorem VariableBound.Fld.ipW_iff {n : ℕ} {x y : List Bool} (hx : x.length = n) (hy : y.length = n) :
    ipW x y = true ↔ AppVariables.ip (fun i : Fin n => bitR (ZMod 2) (x.getD i.val false)) (fun i : Fin n => bitR (ZMod 2) (y.getD i.val false)) = 1 := by sorry
