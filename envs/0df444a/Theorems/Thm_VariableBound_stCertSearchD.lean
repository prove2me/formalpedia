-- Prove2me | Theorems.Thm_VariableBound_stCertSearchD
-- name    : VariableBound.stCertSearchD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:53.597686+00:00
-- url     : https://prove2.me/theorems/3bb3523a-303f-40c8-9e2a-52ad2440ade0
-- title:
--   Variable Bound: st Cert Search D
-- statement:
--   Step 2, the algorithm as a program: the search is polynomial-time in the pad, jointly in
--   everything it reads, if the function that returns X(𝓛) is; m, n̄, β, r̄, t̄ are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L117-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L117-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
set_option autoImplicit false
section
section
open VariableBound
open Groundwork PaddedDescent.F

theorem VariableBound.stCertSearchD : StCertSearchD := by sorry
