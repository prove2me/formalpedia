-- Prove2me | Theorems.Thm_RecursionToBound_thrList_polyT
-- name    : RecursionToBound.thrList_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T07:02:26.590766+00:00
-- url     : https://prove2.me/theorems/2bef30c2-048b-4f52-a5af-468f008af5ef
-- title:
--   Recursion To Bound: thr List poly T
-- statement:
--   The list of the pairs (j, h), each with the threshold θ_(j−h), is polynomial-time jointly in k
--   and r, if k is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L95-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L95-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_UniformInK_CertSparsify_thrList_polyT
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.thrList_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thresholds (k x) (r x) (jh.1 - jh.2)) := by sorry
