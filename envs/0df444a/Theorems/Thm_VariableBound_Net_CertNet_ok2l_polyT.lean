-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ok2l_polyT
-- name    : VariableBound.Net.CertNet.ok2l_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:19:52.384203+00:00
-- url     : https://prove2.me/theorems/7934837c-dcf2-4821-92e3-07c58e4ad225
-- title:
--   Cert Net: ok2l poly T
-- statement:
--   The test of one literal is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L181-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L181-L185

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

theorem VariableBound.Net.CertNet.ok2l_polyT {q a : α → ℕ} {z : α → List Bool} {l : α → ℕ × Bool} (hq : PolyT q) (ha : PolyT a) (hz : PolyT z) (hl : PolyT l) :
    PolyT fun x => ok2l (q x) (a x) (z x) (l x) := by sorry
