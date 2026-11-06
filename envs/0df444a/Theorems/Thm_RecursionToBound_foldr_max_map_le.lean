-- Prove2me | Theorems.Thm_RecursionToBound_foldr_max_map_le
-- name    : RecursionToBound.foldr_max_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:53.305324+00:00
-- url     : https://prove2.me/theorems/56d0b8a2-42a9-4399-aa1f-314f97fc68f1
-- title:
--   Recursion To Bound: foldr max map le
-- statement:
--   The maximum of a list of values that are all at most b is at most b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Top.lean#L55-L60

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Cert ClauseBound.Alg UniformInK VariableBound SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.foldr_max_map_le {β : Type} (f : β → ℕ) (l : List β) {b : ℕ} (h : ∀ a, f a ≤ b) : (l.map f).foldr max 0 ≤ b := by sorry
