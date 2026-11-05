-- Prove2me | Theorems.Thm_PaddedDescent_F_CertNet_mergedF_polyT
-- name    : PaddedDescent.F.CertNet.mergedF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:54.463203+00:00
-- url     : https://prove2.me/theorems/0306c495-1735-481d-b390-ecc8627b64d0
-- title:
--   Cert Net: merged F poly T
-- statement:
--   The Cert Net construction uses the merged F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L208-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L208-L222

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertNet
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F
variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]
variable {C : Type} [Enc C] {Np : PNet C}

theorem PaddedDescent.F.CertNet.mergedF_polyT {F : FNet C} (hF : FKeeps F) {pad : α → U} {K g : α → ℕ} {u : α → X0 C}
    (hp : PolyT pad) (hK : Unary K) (hg : Unary g) (hu : PolyT u) :
    PolyT fun t => mergedF (pad t) (K t) (g t) F (u t) := by sorry
