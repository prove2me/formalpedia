-- Prove2me | Theorems.Thm_RecursionToBound_walkSG_polyT
-- name    : RecursionToBound.walkSG_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:40.999651+00:00
-- url     : https://prove2.me/theorems/c6ef07fd-254f-4096-b6b8-6a88b0cc89dc
-- title:
--   Recursion To Bound: walk SG poly T
-- statement:
--   «Run Steps 2 to 4 on each of the … outputs and add the results»: the walk that adds up is
--   polynomial-time jointly in k, r, the padding string, the root and whatever the value function
--   depends on, if k and 2^k are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L120-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L120-L135

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
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.walkSG_polyT {k : α → ℕ} {r : α → ℕ × ℕ} {pad : α → U} {val : α → CNode → ℕ} {root : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hr : PolyT r)
    (hp : PolyT pad) (hv : PolyT fun q : α × CNode => val q.1 q.2) (hroot : PolyT root) :
    PolyT fun x => _root_.StepSparsify.walkSG (thresholds (k x) (r x)) (k x) (pad x) (val x) (root x) := by sorry
