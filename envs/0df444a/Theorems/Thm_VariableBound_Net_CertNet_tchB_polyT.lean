-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_tchB_polyT
-- name    : VariableBound.Net.CertNet.tchB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:09:33.752702+00:00
-- url     : https://prove2.me/theorems/f066f52f-641a-4876-b92a-df6f30b01489
-- title:
--   Cert Net: tch B poly T
-- statement:
--   The test «the object o touches the node a» is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L57-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_tchB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.tchB_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.tchB_polyT {g n a o : α → ℕ} {D : α → Dat} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (ho : PolyT o) :
    PolyT fun x => tchB (g x) (n x) (D x) (a x) (o x) := by sorry
