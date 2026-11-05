-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_lamNext_unary_aux
-- name    : PaddedDescent.F.CertGrid.lamNext_unary_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:58:38.749399+00:00
-- url     : https://prove2.me/theorems/f86675fa-1300-4056-8792-3a5dadb950d7
-- title:
--   Cert Grid: lam Next unary aux
-- statement:
--   The label length one level down, with any number D in place of Dcol, is given in unary if K, g
--   and the label length are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L115-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L115-L120

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

theorem PaddedDescent.F.CertGrid.lamNext_unary_aux (D : ℕ) {K g n : α → ℕ} (hK : Unary K) (hg : Unary g) (hn : Unary n) :
    Unary fun x => (D * Ubar (g x) (n x) + 3 * g x ^ 2 * capM (g x) (n x)) / (D * K x ^ 2) + 1 := by sorry
