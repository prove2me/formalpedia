-- Prove2me | Theorems.Thm_RecursionToBound_DeltaOf_polyT
-- name    : RecursionToBound.DeltaOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:16.889985+00:00
-- url     : https://prove2.me/theorems/9d80cc69-4da8-43cb-86f3-21fe48274882
-- title:
--   Recursion To Bound: Delta Of poly T
-- statement:
--   The Δ of a formula is polynomial-time jointly in n and the formula, if n is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L69-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L69-L73

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

theorem RecursionToBound.DeltaOf_polyT {n : α → ℕ} {Φ : α → PFml} (hn : Unary n) (hΦ : PolyT Φ) : PolyT fun x => SparsificationLemma.StepSparsify.DeltaOf (n x) (Φ x) := by sorry
