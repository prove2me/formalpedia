-- Prove2me | Theorems.Thm_SingleBitPieces_SecCrossing_PolyA_unary_min_right
-- name    : SingleBitPieces.SecCrossing_PolyA.unary_min_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:21:54.587289+00:00
-- url     : https://prove2.me/theorems/34c88a8e-19fd-4b3e-8fac-52e9268c0d0b
-- title:
--   Sec Crossing Poly A: unary min right
-- statement:
--   The smaller of any number and a number given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecCrossing_PolyA.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecCrossing_PolyA.lean#L37-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_FuelCert
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Log
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork PaddedDescent.F Finset
open SingleBitPieces.SecCrossing_PolyA
variable {α : Type} [Enc α]

theorem SingleBitPieces.SecCrossing_PolyA.unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) := by sorry
