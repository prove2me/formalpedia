-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_sig_polyT
-- name    : VariableBound.Net.CertNet.sig_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:49:22.705699+00:00
-- url     : https://prove2.me/theorems/1b5d9c17-56c8-4615-9e06-a97cb3e76daf
-- title:
--   Cert Net: sig poly T
-- statement:
--   σ_i is polynomial-time for i given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L131-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L131-L134

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

theorem VariableBound.Net.CertNet.sig_polyT {i : α → ℕ} (hi : Unary i) : PolyT fun x => ParityChecks.sig (i x) := by sorry
