-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Series_Qk_eq_Qk__of_360349fc9d8f
-- name    : P2M_GeneralPieces_Series_Qk_eq_Qk__of_360349fc9d8f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:54.291832+00:00
-- url     : https://prove2.me/theorems/9933f3ac-43ba-43d2-a7fb-54ee8b007097
-- title:
--   P2 M General Pieces Series Qk eq Qk  of 360349fc9d8f: P2 M General Pieces Series Qk eq Qk  of 360349fc9d8f
-- statement:
--   Claim (a): Q_s(a,b) does not change if the two factors are exchanged in all its products at
--   once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L86-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L86-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Constant
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_GeneralPieces_Series_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson Finset
variable {A : FA} {b : List ℕ}

theorem P2M_GeneralPieces_Series_Qk_eq_Qk__of_360349fc9d8f (h : StExpansion) (hA : A.Ok b.sum) (hb : Pos b) (s : ℤ) {π σ : Multiset ℕ} (hπ : 0 ∉ π) (hσ : 0 ∉ σ) : Qk A b s π σ = Qk' A b s π σ := by sorry

alias «GeneralPieces».«Series».«Qk_eq_Qk'_of» := P2M_GeneralPieces_Series_Qk_eq_Qk__of_360349fc9d8f
