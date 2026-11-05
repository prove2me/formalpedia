-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_he2
-- name    : PaddedDescent.F.CertSide.he2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:28:08.894292+00:00
-- url     : https://prove2.me/theorems/4acf3e1f-02ba-4614-aa88-2acb18e49620
-- title:
--   Cert Side: he2
-- statement:
--   The Cert Side construction uses the he2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L50-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L50-L51

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

theorem PaddedDescent.F.CertSide.he2 {g ℓ x u : α → ℕ} {z : α → List Bool} (h0 : PolyT g) (h1 : PolyT ℓ) (h2 : PolyT z) (h3 : PolyT x)
    (h4 : PolyT u) : PolyT fun a => he (g a) (ℓ a) (z a) (x a) (u a) := by sorry
