-- Prove2me | Theorems.Thm_Suffices_satLoop_polyTimeSteps_of
-- name    : Suffices.satLoop_polyTimeSteps_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:32:37.081985+00:00
-- url     : https://prove2.me/theorems/45ecc56b-a699-4fa7-9228-ab1ece6b4c2a
-- title:
--   Suffices: sat Loop poly Time Steps of
-- statement:
--   If the machine Mc in the place of Count has polynomial-time steps, so does `satLoop τ Mc` (lines
--   1 to 4 of Algorithm 1). Uses the hypothesis `StFoldUntilPoly` for the loop that can be left early,
--   and the fields `rule_poly` and `out_poly` of the enumeration (Lemma 4: «in time 2^{εn} times a
--   polynomial in n»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L105-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Loop.lean#L105-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)

theorem Suffices.satLoop_polyTimeSteps_of (HP : StFoldUntilPoly) {ε : ℝ} {M τ : ℕ} (hE : Enumerates ε M τ) (Mc : StepMachine Formula ℤ) (hMc : PolyTimeSteps Mc) : PolyTimeSteps (satLoop τ Mc) := by sorry
