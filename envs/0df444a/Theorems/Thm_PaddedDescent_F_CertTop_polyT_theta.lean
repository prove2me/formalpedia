-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_polyT_theta
-- name    : PaddedDescent.F.CertTop.polyT_theta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:37:20.576542+00:00
-- url     : https://prove2.me/theorems/a9e1a527-d71d-407f-a513-cf8dbf057f3d
-- title:
--   Cert Top: poly T theta
-- statement:
--   For every fixed i, the threshold θ i is polynomial-time in τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L53-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L53-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_PaddedDescent_F_CertSparsify
import Theorems.Thm_WidthK_Prog_pickK_eq

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)
variable {α σ : Type} [Enc α] [Enc σ]
omit [Enc σ]

theorem PaddedDescent.F.CertTop.polyT_theta (i : ℕ) {τ : α → ℕ} (hτ : PolyT τ) : PolyT fun x => theta (τ x) i := by sorry
