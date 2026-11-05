-- Prove2me | Theorems.Thm_PaddedDescent_F_CertNet_members2
-- name    : PaddedDescent.F.CertNet.members2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:16:23.045004+00:00
-- url     : https://prove2.me/theorems/761c918d-ad55-4ad5-be59-ba23c017f3d9
-- title:
--   Cert Net: members2
-- statement:
--   The Cert Net construction uses the members2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L36-L37

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

theorem PaddedDescent.F.CertNet.members2 {K g x G : α → ℕ} (hK : PolyT K) (hg : Unary g) (hx : PolyT x) (hG : PolyT G) :
    PolyT fun t => members (K t) (g t) (x t) (G t) := by sorry
