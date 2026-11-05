-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_nRect_polyT
-- name    : PaddedDescent.F.CertGrid.nRect_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:10:10.543204+00:00
-- url     : https://prove2.me/theorems/16fbebb3-eb84-4078-a50a-86f442b04b2d
-- title:
--   Cert Grid: n Rect poly T
-- statement:
--   The number of rectangles is polynomial-time in g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L49-L51

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

theorem PaddedDescent.F.CertGrid.nRect_polyT {g : α → ℕ} (hg : PolyT g) : PolyT fun x => nRect (g x) := by sorry
