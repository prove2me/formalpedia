-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ownB_polyT
-- name    : VariableBound.Net.CertNet.ownB_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:10:50.86504+00:00
-- url     : https://prove2.me/theorems/fb5a9eea-f843-46a1-a683-32fa7ed270f8
-- title:
--   Cert Net: own B poly T
-- statement:
--   The test «a is the owner of the object o» is polynomial-time, for g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L74-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L74-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_ownB_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.ownB_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.ownB_polyT {g n o a : α → ℕ} {D : α → Dat} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ho : PolyT o) (ha : PolyT a) :
    PolyT fun x => ownB (g x) (n x) (D x) (o x) (a x) := by sorry
