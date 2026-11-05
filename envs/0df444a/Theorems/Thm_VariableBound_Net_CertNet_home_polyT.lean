-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_home_polyT
-- name    : VariableBound.Net.CertNet.home_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:09:02.818378+00:00
-- url     : https://prove2.me/theorems/113b5e91-0d18-415f-91d6-aabea00a3485
-- title:
--   Cert Net: home poly T
-- statement:
--   The home of a check is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L53-L54

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

theorem VariableBound.Net.CertNet.home_polyT {g j : α → ℕ} (hg : PolyT g) (hj : PolyT j) : PolyT fun x => home (g x) (j x) := by sorry
