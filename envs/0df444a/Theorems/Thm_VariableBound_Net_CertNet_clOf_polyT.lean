-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_clOf_polyT
-- name    : VariableBound.Net.CertNet.clOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:10:29.69684+00:00
-- url     : https://prove2.me/theorems/fe02362a-7d09-4a0c-93e1-ce1556c7602f
-- title:
--   Cert Net: cl Of poly T
-- statement:
--   The clause of an object is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L49-L50

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

theorem VariableBound.Net.CertNet.clOf_polyT {D : α → Dat} {o : α → ℕ} (hD : PolyT D) (ho : PolyT o) : PolyT fun x => clOf (D x) (o x) := by sorry
