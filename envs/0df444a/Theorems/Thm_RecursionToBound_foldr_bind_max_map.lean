-- Prove2me | Theorems.Thm_RecursionToBound_foldr_bind_max_map
-- name    : RecursionToBound.foldr_bind_max_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:14:27.622401+00:00
-- url     : https://prove2.me/theorems/7033bb3a-cc55-4e0d-a4c7-199384f4a60f
-- title:
--   Recursion To Bound: foldr bind max map
-- statement:
--   The fold of `needOutputsC`, as a function of the list of the numbers that may be missing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L137-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L137-L140

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

theorem RecursionToBound.foldr_bind_max_map (f : ℕ → Option ℕ) (l : List ℕ) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) =
      if (l.map f).all (fun o => o.isSome) then some (((l.map f).map fun o => o.getD 0).foldr max 0) else none := by sorry
