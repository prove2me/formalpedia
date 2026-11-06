-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_WD_polyT
-- name    : VariableBound.Net.CertNet.WD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:46:51.846324+00:00
-- url     : https://prove2.me/theorems/774c2eb1-c4be-421f-b42a-cc995329a6ce
-- title:
--   Cert Net: WD poly T
-- statement:
--   The weight W_a(z_a) is polynomial-time, for g and n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L218-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L218-L222

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

theorem VariableBound.Net.CertNet.WD_polyT {g n y a : α → ℕ} {D : α → Dat} {fl : α → Bool} {z : α → List Bool} (hg : Unary g) (hn : Unary n) (hD : PolyT D) (hy : PolyT y)
    (hfl : PolyT fl) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => WD (g x) (n x) (D x) (y x) (fl x) (a x) (z x) := by sorry
