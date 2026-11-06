-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ok4_polyT
-- name    : VariableBound.Net.CertNet.ok4_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:34:56.771097+00:00
-- url     : https://prove2.me/theorems/832139e5-21e8-49f7-ac22-1d627aad852e
-- title:
--   Cert Net: ok4 poly T
-- statement:
--   The fourth conjunct of `okD` is polynomial-time, for g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L199-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L199-L202

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

theorem VariableBound.Net.CertNet.ok4_polyT {g n y a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (hy : PolyT y) (ha : PolyT a)
    (hz : PolyT z) : PolyT fun x => ok4 (g x) (n x) (D x) (y x) (a x) (z x) := by sorry
