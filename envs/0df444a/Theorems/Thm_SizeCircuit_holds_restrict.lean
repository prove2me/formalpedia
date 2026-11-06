-- Prove2me | Theorems.Thm_SizeCircuit_holds_restrict
-- name    : SizeCircuit.holds_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:46.240749+00:00
-- url     : https://prove2.me/theorems/85fb0d86-191a-44bb-973e-a0b2d8ef1ce7
-- title:
--   Size Circuit: holds restrict
-- statement:
--   A formula on x₀ … xₙ₋₁ holds under an assignment on more variables exactly if it holds under its
--   part on x₀ … xₙ₋₁.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L139-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L139-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.holds_restrict {n m : ℕ} (b : Fin (n + m) → Bool) (x : Fin n → Bool) (hbx : ∀ i, b (Fin.castAdd m i) = x i) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : Holds (ext b) ψ ↔ Holds (ext x) ψ := by sorry
