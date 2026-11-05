-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_sideChk2
-- name    : PaddedDescent.F.CertSide.sideChk2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:30:16.559172+00:00
-- url     : https://prove2.me/theorems/d04e6bc4-dc8e-4098-ba06-38b94b9e3027
-- title:
--   Cert Side: side Chk2
-- statement:
--   The Cert Side construction uses the side Chk2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L118-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L118-L121

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

theorem PaddedDescent.F.CertSide.sideChk2 {g : α → ℕ} {x : α → (ℕ × ℕ) × WQ} (hg : Unary g) (hx : PolyT x) :
    PolyT fun a => sideChk (g a) tr (fun n : ℕ => n) (x a) := by sorry
