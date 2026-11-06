-- Prove2me | Theorems.Thm_RecursionToBound_alphaN_polyT
-- name    : RecursionToBound.alphaN_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:38.759423+00:00
-- url     : https://prove2.me/theorems/1d089142-67a1-4c9d-83bc-1ecd44a4034e
-- title:
--   Recursion To Bound: alpha N poly T
-- statement:
--   α without fractions is polynomial-time jointly in k and r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L62-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L62-L66

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

theorem RecursionToBound.alphaN_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : PolyT k) (hr : PolyT r) : PolyT fun x => alphaN (k x) (r x) := by sorry
