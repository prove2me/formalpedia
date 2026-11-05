-- Prove2me | Theorems.Thm_Paper_achievable_of_eStar_lt
-- name    : Paper.achievable_of_eStar_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:19:06.439803+00:00
-- url     : https://prove2.me/theorems/4874f1a7-63f9-46c6-b8b0-3d83a0eb175e
-- title:
--   Paper: achievable of e Star lt
-- statement:
--   "Let e > e*; then (K, e) is achievable for infinitely many K."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Recursion.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Recursion.lean#L30-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Definitions.Def_Paper_SecLevel_Grid
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_Paper_SecLevel_Recursion
set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog

theorem Paper.achievable_of_eStar_lt {e : ℝ} (he : eStar < e) (K₀ : ℕ) : ∃ K, K₀ ≤ K ∧ Achievable K e := by sorry
