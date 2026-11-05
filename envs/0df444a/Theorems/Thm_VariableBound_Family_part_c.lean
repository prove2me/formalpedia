-- Prove2me | Theorems.Thm_VariableBound_Family_part_c
-- name    : VariableBound.Family.part_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:36:15.145195+00:00
-- url     : https://prove2.me/theorems/c9dd3a38-6139-4446-a9f9-a54521885813
-- title:
--   Family: part c
-- statement:
--   Lemma 13 (Family of checks), part (c): for every set V of more than v = 2^a clauses, |Γ_u ∩ V|
--   is odd for at least |Ω|/4 indices u ∈ Ω, if 1 ≤ a, a − 1 ≤ s, 1 ≤ m and 16m ≤ 2^s;
--   because 5/16 − 1/16 = 1/4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L178-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L178-L192

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

theorem VariableBound.Family.part_c (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    #(Om bits ϑ a) ≤ 4 * #{u ∈ Om bits ϑ a | Odd #(Gam bits ϑ a u ∩ V)} := by sorry
