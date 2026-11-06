-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_mark_polyT
-- name    : VariableBound.Net.CertNet.mark_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:10:48.141417+00:00
-- url     : https://prove2.me/theorems/1b8aa1b8-f5fb-4f21-9f89-f6b196482c92
-- title:
--   Cert Net: mark poly T
-- statement:
--   The mark that a setting gives to an object is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L85-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L85-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_PaddedDescent_F_Mark_Cert_mark_polyT
attribute [local fun_prop] PaddedDescent.F.Mark.Cert.mark_polyT


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]

theorem VariableBound.Net.CertNet.mark_polyT {g n a o : α → ℕ} {D : α → Dat} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hD : PolyT D) (ha : PolyT a) (hz : PolyT z)
    (ho : PolyT o) : PolyT fun x => mark (g x) (n x) (D x) (a x) (z x) (o x) := by sorry
