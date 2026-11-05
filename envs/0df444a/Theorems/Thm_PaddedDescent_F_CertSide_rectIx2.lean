-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_rectIx2
-- name    : PaddedDescent.F.CertSide.rectIx2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:28:12.121122+00:00
-- url     : https://prove2.me/theorems/4eaee72d-e96e-4fc6-90f0-90bb06e23fac
-- title:
--   Cert Side: rect Ix2
-- statement:
--   The Cert Side construction uses the rect Ix2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_PaddedDescent_F_CertSide
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertSide
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]
variable (tr : Bool)

theorem PaddedDescent.F.CertSide.rectIx2 {g p κ : α → ℕ} (h0 : PolyT g) (h1 : PolyT p) (h2 : PolyT κ) :
    PolyT fun x => rectIx (g x) tr (p x) (κ x) := by sorry
