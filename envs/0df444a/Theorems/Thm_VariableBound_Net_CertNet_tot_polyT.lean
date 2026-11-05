-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_tot_polyT
-- name    : VariableBound.Net.CertNet.tot_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:05:20.924535+00:00
-- url     : https://prove2.me/theorems/5d8aff29-7f9a-456e-afd2-37b23b4f0e7d
-- title:
--   Cert Net: tot poly T
-- statement:
--   The sum Σ_a μ_(a,κ) is polynomial-time, for g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L250-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L250-L252

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

theorem VariableBound.Net.CertNet.tot_polyT {g y κ : α → ℕ} {D : α → Dat} (hg : Unary g) (hD : PolyT D) (hy : PolyT y) (hκ : PolyT κ) : PolyT fun x => tot (g x) (D x) (y x) (κ x) := by sorry
