-- Prove2me | Theorems.Thm_RecursionToBound_alphaC_polyT
-- name    : RecursionToBound.alphaC_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:13:35.969005+00:00
-- url     : https://prove2.me/theorems/8455b4b3-3c86-4f68-a936-afd38bf3936d
-- title:
--   Recursion To Bound: alpha C poly T
-- statement:
--   α = ⌈2(k−1)²·ε⁻¹·⌈log₂(32(k−1)²/ε)⌉⌉, for ε = min(a/b, 1), is polynomial-time jointly in k and r =
--   (a, b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L70-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L70-L71

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

theorem RecursionToBound.alphaC_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => Cal.alphaC (k x) (epsOf (r x)) := by sorry
