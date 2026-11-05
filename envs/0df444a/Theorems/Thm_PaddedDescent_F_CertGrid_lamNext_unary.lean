-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_lamNext_unary
-- name    : PaddedDescent.F.CertGrid.lamNext_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:58:26.812776+00:00
-- url     : https://prove2.me/theorems/b72365cd-4296-410a-84b8-e9f1dd137bde
-- title:
--   Cert Grid: lam Next unary
-- statement:
--   The label length one level down is given in unary if K, g and the label length are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L123-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L123-L124

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

theorem PaddedDescent.F.CertGrid.lamNext_unary {K g n : α → ℕ} (hK : Unary K) (hg : Unary g) (hn : Unary n) :
    Unary fun x => lamNext (K x) (g x) (n x) := by sorry
