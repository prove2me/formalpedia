-- Prove2me | Theorems.Thm_VariableBound_Net_CertNet_admD_polyT
-- name    : VariableBound.Net.CertNet.admD_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:49:12.065311+00:00
-- url     : https://prove2.me/theorems/2650ca26-1146-4462-b5b6-1d4956bdff09
-- title:
--   Cert Net: adm D poly T
-- statement:
--   The test «the profile y is admissible» is polynomial-time when g is given in unary and the other
--   arguments, the width k among them, are polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L261-L264
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/CertNet.lean#L261-L264

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

theorem VariableBound.Net.CertNet.admD_polyT {k g n nb M y : α → ℕ} {D : α → Dat} {fl : α → Bool} (hk : PolyT k) (hg : Unary g) (hn : PolyT n) (hnb : PolyT nb) (hM : PolyT M) (hD : PolyT D)
    (hfl : PolyT fl) (hy : PolyT y) : PolyT fun x => admD (k x) (g x) (n x) (nb x) (M x) (D x) (fl x) (y x) := by sorry
