-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_totP_polyT
-- name    : VariableBound.Net.CertNet.totP_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:20:56.426676+00:00
-- url     : https://prove2.me/theorems/5e7b13a4-1055-4783-a14a-78b19d3c13b9
-- title:
--   Cert Net: tot P poly T
-- statement:
--   The sum Σ_({a,b}) μ_(a,b,κ) is polynomial-time, for g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L255-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L255-L257

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

theorem VariableBound.Net.CertNet.totP_polyT {g y κ : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) (hy : PolyT y) (hκ : PolyT κ) : PolyT fun x => totP (g x) (D x) (y x) (κ x) := by sorry
