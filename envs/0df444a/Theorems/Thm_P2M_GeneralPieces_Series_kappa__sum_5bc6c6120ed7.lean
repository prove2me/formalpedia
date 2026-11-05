-- Prove2me | Theorems.Thm_P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7
-- name    : P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:04:19.295529+00:00
-- url     : https://prove2.me/theorems/39fd31ae-3e8a-47e0-8be2-568e5f85d48e
-- title:
--   P2 M General Pieces Series kappa  sum 5bc6c6120ed7: P2 M General Pieces Series kappa  sum 5bc6c6120ed7
-- statement:
--   The sum for κ', "in the same way": Σ_{k ≥ 1} k·C(k−1, j−1)·C(−k−1, n−1)·ω₁^{k−j}·ω₂^{−k−n} =
--   Γ_{j,n}·ε₋^{j+n}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L450-L452
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Deriv.lean#L450-L452

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Scalars
import Mathlib.RingTheory.Derivation.Basic
import Definitions.Def_GeneralPieces_Series_Deriv
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open LaurentPolynomial

theorem P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7 {j n : ℕ} (hj : 1 ≤ j) (hn : 1 ≤ n) :
    (sumM j n fun k => (k : ℚ) * (Ring.choose (k - 1) (j - 1) : ℤ) * (Ring.choose (-k - 1) (n - 1) : ℤ)) = (ClauseBound.Boson.Gam j n : ℚ) • epsM ^ (j + n) := by sorry

alias «GeneralPieces».«Series».«kappa'_sum» := P2M_GeneralPieces_Series_kappa__sum_5bc6c6120ed7
