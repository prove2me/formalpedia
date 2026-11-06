-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_objs_polyT
-- name    : VariableBound.Net.CertNet.objs_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:08:48.467461+00:00
-- url     : https://prove2.me/theorems/a64368f4-41e7-48d6-97c9-c734d7f73fec
-- title:
--   Cert Net: objs poly T
-- statement:
--   The list of the objects is polynomial-time in the formula and the list of checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L41-L42

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

theorem VariableBound.Net.CertNet.objs_polyT {D : α → Dat} (hD : PolyT D) : PolyT fun x => objs (D x) := by sorry
