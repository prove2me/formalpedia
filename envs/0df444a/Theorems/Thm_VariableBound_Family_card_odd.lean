-- Prove2me | Theorems.Thm_VariableBound_Family_card_odd
-- name    : VariableBound.Family.card_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:55.618654+00:00
-- url     : https://prove2.me/theorems/1d972a50-3ad6-4ead-8c43-08c6c318a7b3
-- title:
--   Family: card odd
-- statement:
--   Proof of Lemma 13 (Family of checks): |Γ_u ∩ V| is odd with probability at least 2/3 · 15/32 =
--   5/16, for a set V of more than v = 2^a clauses, if 1 ≤ a, a − 1 ≤ s and 16m ≤ 2^s:
--   16 times the number of these u is at least 5·|𝔽|⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L64-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L64-L91

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

theorem VariableBound.Family.card_odd (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    5 * Fintype.card F ^ 4 ≤ 16 * #{u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)} := by sorry
