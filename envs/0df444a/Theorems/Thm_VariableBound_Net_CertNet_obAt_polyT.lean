-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_obAt_polyT
-- name    : VariableBound.Net.CertNet.obAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:09:17.513093+00:00
-- url     : https://prove2.me/theorems/cc1063a4-03e1-4294-b5f6-6940c281b3a3
-- title:
--   Cert Net: ob At poly T
-- statement:
--   The object at a position is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L45-L46

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

theorem VariableBound.Net.CertNet.obAt_polyT {D : α → Dat} {o : α → ℕ} (hD : PolyT D) (ho : PolyT o) : PolyT fun x => obAt (D x) (o x) := by sorry
