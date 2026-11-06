-- Prove2me | Theorems.Thm_RecursionToBound_DeltaOf_unary
-- name    : RecursionToBound.DeltaOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:14.925207+00:00
-- url     : https://prove2.me/theorems/c12d9cf4-1ff0-4146-899a-a98280391fde
-- title:
--   Recursion To Bound: Delta Of unary
-- statement:
--   The Δ of a formula is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L76-L77

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

theorem RecursionToBound.DeltaOf_unary {n : α → ℕ} {Φ : α → PFml} (hn : Unary n) (hΦ : PolyT Φ) : Unary fun x => SparsificationLemma.StepSparsify.DeltaOf (n x) (Φ x) := by sorry
