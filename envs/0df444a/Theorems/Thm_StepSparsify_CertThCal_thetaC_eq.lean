-- Prove2me | Theorems.Thm_StepSparsify_CertThCal_thetaC_eq
-- name    : StepSparsify.CertThCal.thetaC_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:53:05.686247+00:00
-- url     : https://prove2.me/theorems/13585cd2-7a20-479d-817b-24e37a5934f2
-- title:
--   Cert Th Cal: theta C eq
-- statement:
--   Calabro's thresholds in closed form: θ 0 = 2, and θ i = α·(2·(8α)^(i−1)·Cat_(i−1)) for i ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertThCal.lean#L34-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertThCal.lean#L34-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Mathlib.Data.Nat.Choose.Central
import Definitions.Def_StepSparsify_CertThCal
set_option autoImplicit false
section
section
open StepSparsify StepSparsify.CertThCal
open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem StepSparsify.CertThCal.thetaC_eq (a i : ℕ) : Cal.thetaC a i = if i = 0 then 2 else a * (2 * (8 * a) ^ (i - 1) * catalan (i - 1)) := by sorry
