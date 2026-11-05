-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ok1_polyT
-- name    : VariableBound.Net.CertNet.ok1_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:15:09.857116+00:00
-- url     : https://prove2.me/theorems/2453baf3-a943-4dce-ac62-68515d672d7d
-- title:
--   Cert Net: ok1 poly T
-- statement:
--   The first conjunct of `okD` is polynomial-time, for g and n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L174-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L174-L178

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

theorem VariableBound.Net.CertNet.ok1_polyT {g n a : α → ℕ} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => ok1 (g x) (n x) (a x) (z x) := by sorry
