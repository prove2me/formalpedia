-- Prove2me | Theorems.Thm_VariableBound_Family_card_Om_add
-- name    : VariableBound.Family.card_Om_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:46:37.115753+00:00
-- url     : https://prove2.me/theorems/368e50e4-14f4-4d08-bacf-e854f3a4e0ec
-- title:
--   Family: card Om add
-- statement:
--   Ω and the set of the u with |Γ_u| > 16m/v together are 𝔽⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L139-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L139-L141

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

theorem VariableBound.Family.card_Om_add (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) :
    #(Om bits ϑ a) + #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} = Fintype.card F ^ 4 := by sorry
