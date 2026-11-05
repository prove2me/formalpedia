-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_sideWF2
-- name    : PaddedDescent.F.CertSide.sideWF2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:38.166265+00:00
-- url     : https://prove2.me/theorems/cdb6b365-9320-4e9b-86dd-e045c4ff4640
-- title:
--   Cert Side: side WF2
-- statement:
--   The Cert Side construction uses the side WF2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L128-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L128-L131

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

theorem PaddedDescent.F.CertSide.sideWF2 {g ℓ y : α → ℕ} {T : α → Tab} {q : α → WQ} (hg : Unary g) (hℓ : PolyT ℓ) (hy : PolyT y) (hT : PolyT T)
    (hq : PolyT q) : PolyT fun x => sideWF (g x) tr (ℓ x) (y x) (T x) (q x) := by sorry
