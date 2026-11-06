-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_linkB_polyT
-- name    : VariableBound.Net.CertNet.linkB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:10:29.076172+00:00
-- url     : https://prove2.me/theorems/1206b5b3-8d72-4140-bb8c-e163f84c3c18
-- title:
--   Cert Net: link B poly T
-- statement:
--   The test «{a, b} is a test of the object o» is polynomial-time; g is in unary because the test
--   runs through all nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L68-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_linkB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.linkB_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.linkB_polyT {g n o a b : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ho : PolyT o) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun x => linkB (g x) (n x) (D x) (o x) (a x) (b x) := by sorry
