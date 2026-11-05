-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_nRect_eq_mul
-- name    : PaddedDescent.F.CertGrid.nRect_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:15:31.540085+00:00
-- url     : https://prove2.me/theorems/5828bd96-9240-499f-bb50-de6c46cd7888
-- title:
--   Cert Grid: n Rect eq mul
-- statement:
--   The number of rectangles is the square of g(g−1)/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L38-L40

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

theorem PaddedDescent.F.CertGrid.nRect_eq_mul (g : ℕ) : nRect g = g * (g - 1) / 2 * (g * (g - 1) / 2) := by sorry
