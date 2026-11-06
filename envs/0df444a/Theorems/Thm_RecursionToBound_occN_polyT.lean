-- Prove2me | Theorems.Thm_RecursionToBound_occN_polyT
-- name    : RecursionToBound.occN_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:23:01.85245+00:00
-- url     : https://prove2.me/theorems/9c126b47-d23f-4dd6-9c2b-51547179836b
-- title:
--   Recursion To Bound: occ N poly T
-- statement:
--   The number of clauses in which a variable occurs is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L50-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Exponent
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_StepSparsify_CertWalk
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Top
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.occN_polyT {Φ : α → PFml} {v : α → ℕ} (hΦ : PolyT Φ) (hv : PolyT v) : PolyT fun x => occN (Φ x) (v x) := by sorry
