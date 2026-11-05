-- Prove2me | Theorems.Thm_UniformInK_CertBoth_allOccU_polyT
-- name    : UniformInK.CertBoth.allOccU_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:02.804983+00:00
-- url     : https://prove2.me/theorems/1fb4e8e1-839b-448b-8e78-175191022466
-- title:
--   Cert Both: all Occ U poly T
-- statement:
--   The test whether every variable occurs is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Both.lean#L25-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Both.lean#L25-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_UniformInK_Cert_Both
set_option autoImplicit false
section
section
open UniformInK UniformInK.CertBoth
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

theorem UniformInK.CertBoth.allOccU_polyT : PolyT allOccU := by sorry
