-- Prove2me | Theorems.Thm_StepSparsify_stServesCal
-- name    : StepSparsify.stServesCal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:26.214207+00:00
-- url     : https://prove2.me/theorems/0c271a08-8ce0-48ea-9234-6a60f8b05401
-- title:
--   Step Sparsify: st Serves Cal
-- statement:
--   Calabro's thresholds serve, if they are polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L78-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L78-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_StepSparsify_CalServes
set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma

theorem StepSparsify.stServesCal (hT : StCertThCal) : StServesCal := by sorry
