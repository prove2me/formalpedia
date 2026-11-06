-- Prove2me | Theorems.Thm_RecursionToBound_occBound_polyT
-- name    : RecursionToBound.occBound_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:33.976715+00:00
-- url     : https://prove2.me/theorems/0dd67b5c-0171-4c75-a906-21401f8398fd
-- title:
--   Recursion To Bound: occ Bound poly T
-- statement:
--   The bound on the occurrences, 2·(θ₀ + … + θ_(k−1)) + 2, is polynomial-time jointly in k and r,
--   if k is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L79-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Thresholds.lean#L79-L89

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

theorem RecursionToBound.occBound_polyT {k : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) : PolyT fun x => occBound (k x) (r x) := by sorry
