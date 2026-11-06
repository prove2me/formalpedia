-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ok3_polyT
-- name    : VariableBound.Net.CertNet.ok3_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:31:59.027881+00:00
-- url     : https://prove2.me/theorems/b9e36ba2-25ce-4b45-bf55-33a1b1502022
-- title:
--   Cert Net: ok3 poly T
-- statement:
--   The third conjunct of `okD` is polynomial-time, for g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L193-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L193-L196

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

theorem VariableBound.Net.CertNet.ok3_polyT {g n y a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a)
    (hz : PolyT z) : PolyT fun x => ok3 (g x) (n x) (D x) (y x) (a x) (z x) := by sorry
