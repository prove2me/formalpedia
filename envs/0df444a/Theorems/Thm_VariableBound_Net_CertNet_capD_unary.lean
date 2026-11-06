-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_capD_unary
-- name    : VariableBound.Net.CertNet.capD_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:40.115291+00:00
-- url     : https://prove2.me/theorems/f444a264-5897-4c27-88d7-2eea8d869f1d
-- title:
--   Cert Net: cap D unary
-- statement:
--   The number c_(a,b) of bits of a label is given in unary, for g in unary, given the certificate
--   that ⌈log C(t, μ)⌉ is given in unary (`StCertRank`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L106-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L106-L111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.capD_unary (h : StCertRank) {g n y a b : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b) :
    Unary fun x => capD (g x) (n x) (D x) (y x) (a x) (b x) := by sorry
