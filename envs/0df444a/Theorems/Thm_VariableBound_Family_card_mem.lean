-- Prove2me | Theorems.Thm_VariableBound_Family_card_mem
-- name    : VariableBound.Family.card_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:59.175426+00:00
-- url     : https://prove2.me/theorems/c74c38b5-898e-4728-adc2-75c462c042ee
-- title:
--   Family: card mem
-- statement:
--   Proof of Lemma 13 (Family of checks): a clause lies in Γ_u with probability at most 1/v, v =
--   2^a, if 1 ≤ a and a − 1 ≤ s: v times the number of these u is at most |𝔽|⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L95-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L95-L112

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

theorem VariableBound.Family.card_mem (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ a * #{u : F × F × F × F | E ∈ Gam bits ϑ a u} ≤ Fintype.card F ^ 4 := by sorry
