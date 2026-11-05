-- Prove2me | Theorems.Thm_RecursionToBound_thresholds_polyT
-- name    : RecursionToBound.thresholds_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:13:59.128954+00:00
-- url     : https://prove2.me/theorems/eae5d8ef-0c86-4c28-aef2-ec6e65a870ce
-- title:
--   Recursion To Bound: thresholds poly T
-- statement:
--   The threshold θ_i is polynomial-time jointly in k, r and i, if i is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L74-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L74-L75

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

theorem RecursionToBound.thresholds_polyT {k i : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) (hi : Unary i) : PolyT fun x => thresholds (k x) (r x) (i x) := by sorry
