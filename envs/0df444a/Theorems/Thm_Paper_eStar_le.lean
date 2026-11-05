-- Prove2me | Theorems.Thm_Paper_eStar_le
-- name    : Paper.eStar_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:20:20.516197+00:00
-- url     : https://prove2.me/theorems/1d01f893-d042-4836-9693-04c355e23877
-- title:
--   Paper: e Star le
-- statement:
--   If (K, e) is achievable for infinitely many K, then e* ≤ e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Recursion.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Paper/SecLevel_Recursion.lean#L38-L39

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

theorem Paper.eStar_le {e : ℝ} (h0 : 0 ≤ e) (h : ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e) : eStar ≤ e := by sorry
