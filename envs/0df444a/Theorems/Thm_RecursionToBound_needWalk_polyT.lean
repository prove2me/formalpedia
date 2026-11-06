-- Prove2me | Theorems.Thm_RecursionToBound_needWalk_polyT
-- name    : RecursionToBound.needWalk_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:14:34.707076+00:00
-- url     : https://prove2.me/theorems/314e3791-ad1c-423b-b927-3f4b60105fc1
-- title:
--   Recursion To Bound: need Walk poly T
-- statement:
--   The exponent for the walk is polynomial-time jointly in k, r and n, if k is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L74-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L74-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Exponent
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.needWalk_polyT {k n : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) (hn : PolyT n) : PolyT fun x => needWalk (k x) (r x) (n x) := by sorry
