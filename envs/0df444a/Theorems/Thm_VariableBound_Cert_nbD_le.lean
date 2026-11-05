-- Prove2me | Theorems.Thm_VariableBound_Cert_nbD_le
-- name    : VariableBound.Cert.nbD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:37.05753+00:00
-- url     : https://prove2.me/theorems/0b3dedaa-a561-44c6-ae8f-d3a8ba2ec1a6
-- title:
--   Cert: nb D le
-- statement:
--   n̄ ≤ n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Cert.lean#L46-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Cert.lean#L46-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]

theorem VariableBound.Cert.nbD_le (n Δ : ℕ) : nbD n Δ ≤ n + 1 := by sorry
