-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_sideCapU
-- name    : PaddedDescent.F.CertSide.sideCapU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:36.118749+00:00
-- url     : https://prove2.me/theorems/52841d20-4070-42a1-a877-7eb2d988de07
-- title:
--   Cert Side: side Cap U
-- statement:
--   The Cert Side construction uses the side Cap U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L91-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L91-L94

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

theorem PaddedDescent.F.CertSide.sideCapU {g n y a b : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => sideCap (g x) tr (n x) (y x) (a x) (b x) := by sorry
