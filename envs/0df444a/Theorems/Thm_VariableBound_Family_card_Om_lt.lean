-- Prove2me | Theorems.Thm_VariableBound_Family_card_Om_lt
-- name    : VariableBound.Family.card_Om_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:54.811265+00:00
-- url     : https://prove2.me/theorems/82a864dc-8193-4d30-8aa8-1a122adce4a9
-- title:
--   Family: card Om lt
-- statement:
--   Lemma 13 (Family of checks): |Ω| < (32m)⁴, if 2^s < 32m, because |Ω| ≤ |𝔽|⁴ = 2^(4s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L152-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L152-L155

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
omit [DecidableEq F]

theorem VariableBound.Family.card_Om_lt (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (h32 : 2 ^ s < 32 * m) : #(Om bits ϑ a) < (32 * m) ^ 4 := by sorry
