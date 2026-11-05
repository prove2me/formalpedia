-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b
-- name    : P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:36.639476+00:00
-- url     : https://prove2.me/theorems/9d39706b-a419-4992-b840-f4a1dd03d263
-- title:
--   P2 M General Pieces Ring to N map to PNat  be122ac80f3b: P2 M General Pieces Ring to N map to PNat  be122ac80f3b
-- statement:
--   The parts of a partition, made positive integers and natural numbers again.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L44-L48

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

theorem P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b {s : Multiset ℕ} (hs : ∀ i ∈ s, 0 < i) : toN (s.map Nat.toPNat') = s := by sorry

alias «GeneralPieces».«Ring».«toN_map_toPNat'» := P2M_GeneralPieces_Ring_toN_map_toPNat__be122ac80f3b
