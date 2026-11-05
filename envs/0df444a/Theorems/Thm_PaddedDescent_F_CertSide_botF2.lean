-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_botF2
-- name    : PaddedDescent.F.CertSide.botF2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:30:26.976459+00:00
-- url     : https://prove2.me/theorems/562317b9-5383-4873-a8fa-3db579451585
-- title:
--   Cert Side: bot F2
-- statement:
--   The Cert Side construction uses the bot F2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L98-L100

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

theorem PaddedDescent.F.CertSide.botF2 {pad : α → U} {i : α → ℕ} {x y w : α → List Bool} (hp : PolyT pad) (hi : PolyT i) (hx : PolyT x)
    (hy : PolyT y) (hw : PolyT w) : PolyT fun a => botF (pad a) tr (i a) (x a) (y a) (w a) := by sorry
