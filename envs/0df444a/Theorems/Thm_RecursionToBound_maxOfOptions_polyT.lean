-- Prove2me | Theorems.Thm_RecursionToBound_maxOfOptions_polyT
-- name    : RecursionToBound.maxOfOptions_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:15:14.880204+00:00
-- url     : https://prove2.me/theorems/447dee8e-98cc-4a7c-a493-4271132f0672
-- title:
--   Recursion To Bound: max Of Options poly T
-- statement:
--   The function whose value is `none` if one of the numbers is `none`, and otherwise the maximum of
--   the list, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L144-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L144-L147

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
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.maxOfOptions_polyT {l : α → List (Option ℕ)} (hl : PolyT l) :
    PolyT fun x => if (l x).all (fun o => o.isSome) then some (((l x).map fun o => o.getD 0).foldr max 0) else none := by sorry
