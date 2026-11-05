-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_polyT_pickKU
-- name    : PaddedDescent.F.CertTop.polyT_pickKU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:37:21.717902+00:00
-- url     : https://prove2.me/theorems/1350fa4d-20de-49d2-bef7-10be062b8d59
-- title:
--   Cert Top: poly T pick KU
-- statement:
--   The choice of the heart and its petals at a node is polynomial-time jointly in τ and the
--   formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L60-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L60-L64

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

theorem PaddedDescent.F.CertTop.polyT_pickKU (k : ℕ) {τ : α → ℕ} {s : α → PFml} (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => pickK (theta (τ x)) k (s x) := by sorry
