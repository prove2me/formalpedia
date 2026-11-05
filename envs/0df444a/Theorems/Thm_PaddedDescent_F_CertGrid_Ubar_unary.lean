-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_Ubar_unary
-- name    : PaddedDescent.F.CertGrid.Ubar_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:58:11.126667+00:00
-- url     : https://prove2.me/theorems/28c42390-abe7-4e06-87bc-2f247e2ac731
-- title:
--   Cert Grid: Ubar unary
-- statement:
--   The bound on U of the cheaper side network is given in unary if g and the label length are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L110-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L110-L111

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

theorem PaddedDescent.F.CertGrid.Ubar_unary {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => Ubar (g x) (n x) := by sorry
