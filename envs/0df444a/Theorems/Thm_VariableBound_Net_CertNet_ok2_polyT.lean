-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ok2_polyT
-- name    : VariableBound.Net.CertNet.ok2_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:30:28.280606+00:00
-- url     : https://prove2.me/theorems/729f538e-7253-4587-84f3-fe35c05b4d5a
-- title:
--   Cert Net: ok2 poly T
-- statement:
--   The second conjunct of `okD` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L188-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L188-L190

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

theorem VariableBound.Net.CertNet.ok2_polyT {g n a : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z) :
    PolyT fun x => ok2 (g x) (n x) (D x) (a x) (z x) := by sorry
