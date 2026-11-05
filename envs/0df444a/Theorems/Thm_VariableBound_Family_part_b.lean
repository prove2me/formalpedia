-- Prove2me | Theorems.Thm_VariableBound_Family_part_b
-- name    : VariableBound.Family.part_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:36:05.860299+00:00
-- url     : https://prove2.me/theorems/f33b725b-3fda-4a0f-a611-5c2a59cea4c6
-- title:
--   Family: part b
-- statement:
--   Lemma 13 (Family of checks), part (b): every clause lies in Γ_u for at most (16/(15v))·|Ω|
--   indices u ∈ Ω, v = 2^a, if 1 ≤ a, a − 1 ≤ s and 1 ≤ m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L166-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L166-L173

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}

theorem VariableBound.Family.part_b (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (E : Fin m) :
    15 * 2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} ≤ 16 * #(Om bits ϑ a) := by sorry
