-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133
-- name    : P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:36.903164+00:00
-- url     : https://prove2.me/theorems/a1732db5-b555-4c6c-afe4-1944cd442328
-- title:
--   P2 M General Pieces Ring map to PNat  to N 169eea647133: P2 M General Pieces Ring map to PNat  to N 169eea647133
-- statement:
--   Back from natural numbers to positive integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L37-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L37-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133 (μ : Ptn) : (toN μ).map Nat.toPNat' = μ := by sorry

alias «GeneralPieces».«Ring».«map_toPNat'_toN» := P2M_GeneralPieces_Ring_map_toPNat__toN_169eea647133
