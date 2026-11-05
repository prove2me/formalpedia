-- Prove2me | Theorems.Thm_SingleBitPieces_exponent_eq
-- name    : SingleBitPieces.exponent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:57:48.831012+00:00
-- url     : https://prove2.me/theorems/b5391ccd-6c84-4d8a-aa43-9a036ec99f6a
-- title:
--   Single Bit Pieces: exponent eq
-- statement:
--   The exponent e·U + (e + 2)·gP/K equals the paper's exponent e(U + gP/K) + 2gP/K of Lemma 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecNetworks_LemGrouping.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/SingleBitPieces/SecNetworks_LemGrouping.lean#L28-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
set_option autoImplicit false
section
section
open SingleBitPieces
open Groundwork Groundwork.Prog Finset Paper NetE Stepped

theorem SingleBitPieces.exponent_eq (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * g * P / K := by sorry
