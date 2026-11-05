-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_childF_polyT
-- name    : PaddedDescent.F.CertGrid.childF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:58:32.777713+00:00
-- url     : https://prove2.me/theorems/5df414c2-7e46-424b-ad6f-96fc0ec29fa3
-- title:
--   Cert Grid: child F poly T
-- statement:
--   The child of one pattern.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L127-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L127-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertGrid.childF_polyT (hR : StCertRebalG) (hS : StCertSide) {pad : α → U} {L : α → Lvl} {I : α → PInst} {y : α → ℕ}
    (hp : PolyT pad) (hL : PolyT L) (hI : PolyT I) (hy : PolyT y) : PolyT fun x => childF (pad x) (L x) (I x) (y x) := by sorry
