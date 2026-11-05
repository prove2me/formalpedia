-- Prove2me | Theorems.Thm_VariableBound_Cert_filter_range_polyT
-- name    : VariableBound.Cert.filter_range_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:52:00.004924+00:00
-- url     : https://prove2.me/theorems/5f74da5d-7b18-4c79-9daf-f79c53e37fea
-- title:
--   Cert: filter range poly T
-- statement:
--   The list of the i < n that pass a test is polynomial-time, for n in unary; the test is only
--   needed for indices given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Cert.lean#L34-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Cert.lean#L34-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]

theorem VariableBound.Cert.filter_range_polyT {n : α → ℕ} {f : α → ℕ → Bool} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).filter (f x) := by sorry
