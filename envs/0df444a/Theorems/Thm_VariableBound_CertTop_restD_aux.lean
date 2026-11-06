-- Prove2me | Theorems.Thm_VariableBound_CertTop_restD_aux
-- name    : VariableBound.CertTop.restD_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:05:51.711199+00:00
-- url     : https://prove2.me/theorems/42e0b01c-3f08-4e82-880f-fa5a46962496
-- title:
--   Cert Top: rest D aux
-- statement:
--   The formula of the exponent for everything but the networks is polynomial-time when every number
--   in it is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L46-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L46-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Cert_Top
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary

set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {k K n s : α → ℕ}

theorem VariableBound.CertTop.restD_aux {Z₁ Z₂ B z q : α → ℕ} (hk : PolyT k) (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 2 * Z₁ x + Z₂ x + (n x / q x + 2) + (B x + 5 * k x + 10 + (k x + 3) * z x) := by sorry
