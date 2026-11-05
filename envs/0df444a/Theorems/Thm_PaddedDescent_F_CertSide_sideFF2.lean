-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_sideFF2
-- name    : PaddedDescent.F.CertSide.sideFF2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:45.502038+00:00
-- url     : https://prove2.me/theorems/22d57d75-2270-4480-b316-59c2febb65ab
-- title:
--   Cert Side: side FF2
-- statement:
--   The Cert Side construction uses the side FF2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L133-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L133-L137

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

theorem PaddedDescent.F.CertSide.sideFF2 {pad : α → U} {g ℓ y : α → ℕ} {q : α → FQ} (hp : PolyT pad) (hg : Unary g) (hℓ : Unary ℓ) (hy : PolyT y)
    (hq : PolyT q) : PolyT fun x => sideFF (pad x) (g x) tr (ℓ x) (y x) (q x) := by sorry
