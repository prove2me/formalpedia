-- Prove2me | Theorems.Thm_RecursionToBound_stackLen_aux
-- name    : RecursionToBound.stackLen_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:13:40.952897+00:00
-- url     : https://prove2.me/theorems/da1fa20f-ee0f-4579-b124-0684611ef306
-- title:
--   Recursion To Bound: stack Len aux
-- statement:
--   The formula of the bound on the length of the walk's state is polynomial-time when every number
--   in it is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L55-L60

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

theorem RecursionToBound.stackLen_aux {b p m k n : α → ℕ} (hb : PolyT b) (hp : PolyT p) (hm : PolyT m) (hk : PolyT k) (hn : PolyT n) :
    PolyT fun x => (b x * n x + 1) * (p x * m x * (k x * (3 * n x + 5) + 10) + 2 * n x * (2 * (3 * n x + 5) + 10) + 8) + 3 * n x + 16 := by sorry
