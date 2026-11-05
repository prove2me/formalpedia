-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_sideCtx_polyT
-- name    : PaddedDescent.F.CertGrid.sideCtx_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:10:00.052495+00:00
-- url     : https://prove2.me/theorems/6727429a-8404-4ef1-8670-50f1c07c8cc7
-- title:
--   Cert Grid: side Ctx poly T
-- statement:
--   The context of the cheaper side network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L91-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L91-L97

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

theorem PaddedDescent.F.CertGrid.sideCtx_polyT {pad gu : α → U} {I : α → PInst} {y : α → ℕ} (hp : PolyT pad) (hg : PolyT gu) (hI : PolyT I)
    (hy : PolyT y) : PolyT fun x => sideCtx (pad x) (gu x) (I x) (y x) := by sorry
