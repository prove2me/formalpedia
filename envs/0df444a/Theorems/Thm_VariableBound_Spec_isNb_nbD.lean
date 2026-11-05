-- Prove2me | Theorems.Thm_VariableBound_Spec_isNb_nbD
-- name    : VariableBound.Spec.isNb_nbD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:40:46.288266+00:00
-- url     : https://prove2.me/theorems/08a02f27-a3f2-43b8-8b29-165cd90c1639
-- title:
--   Spec: is Nb nb D
-- statement:
--   The computed n̄ is the n̄ of the text, if Δ ≥ 1 and 2Δ ≤ 2^n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L80-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Spec.lean#L80-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec

theorem VariableBound.Spec.isNb_nbD (n Δ : ℕ) (hΔ : 1 ≤ Δ) (h : 2 * Δ ≤ 2 ^ n) : IsNb n Δ (nbD n Δ) := by sorry
