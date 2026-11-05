-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_bruteF_polyT
-- name    : PaddedDescent.F.CertGrid.bruteF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:02.570856+00:00
-- url     : https://prove2.me/theorems/7652dd23-c26f-4e72-8c6c-51997d6bd297
-- title:
--   Cert Grid: brute F poly T
-- statement:
--   Brute force on K nodes, K a constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L151-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L151-L165

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

theorem PaddedDescent.F.CertGrid.bruteF_polyT (K : ℕ) {pad : α → U} {I : α → PInst} (hp : PolyT pad) (hI : PolyT I) :
    PolyT fun x => bruteF (pad x) K (I x) := by sorry
