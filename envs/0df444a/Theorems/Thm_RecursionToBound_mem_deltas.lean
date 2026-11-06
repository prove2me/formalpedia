-- Prove2me | Theorems.Thm_RecursionToBound_mem_deltas
-- name    : RecursionToBound.mem_deltas
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:15:09.864065+00:00
-- url     : https://prove2.me/theorems/864af57c-80e5-4bc3-a4ad-d4604c892cf2
-- title:
--   Recursion To Bound: mem deltas
-- statement:
--   The numbers Δ of the list are at least 2, at most n + 1 and at most the bound on the
--   occurrences.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L121-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L121-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Exponent
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.mem_deltas {k n Δ : ℕ} {r : ℕ × ℕ} (h : Δ ∈ deltas k r n) : 2 ≤ Δ ∧ Δ ≤ n + 1 ∧ Δ ≤ occBound k r := by sorry
