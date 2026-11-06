-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_tch_polyT
-- name    : VariableBound.Net.CertNet.tch_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:09:48.924843+00:00
-- url     : https://prove2.me/theorems/c1cbae96-8487-41ba-b376-98818792e0a0
-- title:
--   Cert Net: tch poly T
-- statement:
--   The list of the objects that touch a node is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L62-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L62-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_tch_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.tch_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.tch_polyT {g n a : α → ℕ} {D : α → Dat} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) :
    PolyT fun x => tch (g x) (n x) (D x) (a x) := by sorry
