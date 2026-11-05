-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_ite_zero_polyT
-- name    : VariableBound.Net.CertNet.ite_zero_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:48:22.723841+00:00
-- url     : https://prove2.me/theorems/bacb01d3-0eb0-4c22-9930-2b6bdd35bfa5
-- title:
--   Cert Net: ite zero poly T
-- statement:
--   A choice between two integers by the test «i = 0» is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L127-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L127-L128

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

theorem VariableBound.Net.CertNet.ite_zero_polyT {i : α → ℕ} {u v : α → ℤ} (hi : PolyT i) (hu : PolyT u) (hv : PolyT v) : PolyT fun x => if i x = 0 then u x else v x := by sorry
