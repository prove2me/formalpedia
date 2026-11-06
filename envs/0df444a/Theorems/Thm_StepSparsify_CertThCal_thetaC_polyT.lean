-- Prove2me | Theorems.Thm_StepSparsify_CertThCal_thetaC_polyT
-- name    : StepSparsify.CertThCal.thetaC_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:08:18.065229+00:00
-- url     : https://prove2.me/theorems/12ef3138-19e9-40d1-81b8-3c6f003b98db
-- title:
--   Cert Th Cal: theta C poly T
-- statement:
--   The threshold θ i is polynomial-time whenever Calabro's α (here `a`) is polynomial-time and i is
--   given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertThCal.lean#L46-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CertThCal.lean#L46-L51

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

theorem StepSparsify.CertThCal.thetaC_polyT {a i : α → ℕ} (ha : PolyT a) (hi : Unary i) : PolyT fun x => Cal.thetaC (a x) (i x) := by sorry
