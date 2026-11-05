-- Prove2me | Theorems.Thm_PaddedDescent_F_CertNet_tabulate_polyT
-- name    : PaddedDescent.F.CertNet.tabulate_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:31:46.334724+00:00
-- url     : https://prove2.me/theorems/9599f378-11c9-4e02-b01b-39f2a5ebdd8f
-- title:
--   Cert Net: tabulate poly T
-- statement:
--   The Cert Net construction uses the tabulate poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L174-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean#L174-L186

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

theorem PaddedDescent.F.CertNet.tabulate_polyT {pad : α → U} {K ℓ : α → ℕ} {F : α → IQ → ℤ} (hp : PolyT pad) (hK : Unary K) (hℓ : Unary ℓ)
    (hF : PolyT fun p : α × IQ => F p.1 p.2) : PolyT fun t => tabulate (pad t) (K t) (ℓ t) (F t) := by sorry
