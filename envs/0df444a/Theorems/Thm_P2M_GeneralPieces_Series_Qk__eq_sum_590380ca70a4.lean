-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4
-- name    : P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:19:42.077052+00:00
-- url     : https://prove2.me/theorems/91c244d6-e0ce-45e5-af30-5ac3b062993e
-- title:
--   P2 M General Pieces Series Qk  eq sum 590380ca70a4: P2 M General Pieces Series Qk  eq sum 590380ca70a4
-- statement:
--   The same with the factors exchanged.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L65-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/LemmaQ.lean#L65-L72

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

theorem P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4 (hA : A.Ok b.sum) (s : ℤ) (π σ : Multiset ℕ) : Qk' A b s π σ = (A.map fun c => c.1 * qM c.2 b s π σ).sum := by sorry

alias «GeneralPieces».«Series».«Qk'_eq_sum» := P2M_GeneralPieces_Series_Qk__eq_sum_590380ca70a4
