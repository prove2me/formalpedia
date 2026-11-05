-- Prove2me | Theorems.Thm_RecursionToBound_stepC_polyT
-- name    : RecursionToBound.stepC_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:57:45.62812+00:00
-- url     : https://prove2.me/theorems/033a81c3-601c-46dd-876d-8fc3d650a081
-- title:
--   Recursion To Bound: step C poly T
-- statement:
--   The two children of a node of the tree of the sparsification with the thresholds for k and ε are
--   polynomial-time jointly in k, r and the node, if k and 2^k are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L107-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L107-L113

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

theorem RecursionToBound.stepC_polyT {k : α → ℕ} {r : α → ℕ × ℕ} {x : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hr : PolyT r) (hx : PolyT x) :
    PolyT fun a => stepC (thresholds (k a) (r a)) (k a) (x a) := by sorry
