-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_str_polyT
-- name    : VariableBound.Net.CertNet.str_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:10:49.76374+00:00
-- url     : https://prove2.me/theorems/6c3e3357-93e3-4d87-a7be-ae0ff32c1d5e
-- title:
--   Cert Net: str poly T
-- statement:
--   The string of the marks of the objects of a kind with a given test is polynomial-time, for g in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L92-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L92-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_str_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.str_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.str_polyT {g n a b κ : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hb : PolyT b)
    (hκ : PolyT κ) (hz : PolyT z) : PolyT fun x => str (g x) (n x) (D x) (a x) (b x) (κ x) (z x) := by sorry
