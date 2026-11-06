-- Prove2me | Theorems.Thm_RecursionToBound_DeltaOf_le
-- name    : RecursionToBound.DeltaOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:34.032671+00:00
-- url     : https://prove2.me/theorems/b8c9a888-98bc-46fa-8efb-508cec950313
-- title:
--   Recursion To Bound: Delta Of le
-- statement:
--   The Δ of a formula is at most its number of clauses plus 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L63-L66

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.DeltaOf_le (n : ℕ) (Φ : PFml) : SparsificationLemma.StepSparsify.DeltaOf n Φ ≤ Φ.length + 2 := by sorry
