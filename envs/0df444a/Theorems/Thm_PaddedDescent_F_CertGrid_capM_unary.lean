-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_capM_unary
-- name    : PaddedDescent.F.CertGrid.capM_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:48:51.916872+00:00
-- url     : https://prove2.me/theorems/bc52aa3b-85d6-47b2-ace5-4de4c9d1000e
-- title:
--   Cert Grid: cap M unary
-- statement:
--   The bound on the label bits that two nodes of a side network share is given in unary (`Unary`)
--   if g and the label length are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L106-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L106-L107

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

theorem PaddedDescent.F.CertGrid.capM_unary {g n : α → ℕ} (hg : Unary g) (hn : Unary n) : Unary fun x => capM (g x) (n x) := by sorry
