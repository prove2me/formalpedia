-- Prove2me | Theorems.Thm_VariableBound_Family_mem_Gam
-- name    : VariableBound.Family.mem_Gam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:52.753018+00:00
-- url     : https://prove2.me/theorems/4886baae-5c85-4f02-a73a-998224590bdc
-- title:
--   Family: mem Gam
-- statement:
--   A clause E lies in Γ_u if and only if H_E holds for the pair (u₁, u₂) and ⟨u₃^E, u₄⟩ = 1 for the
--   pair (u₃, u₄). This is the definition of Γ_u, written with the two pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L57-L59

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
omit [Fintype F] [DecidableEq F]

theorem VariableBound.Family.mem_Gam (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) (E : Fin m) :
    E ∈ Gam bits ϑ a u ↔ H bits ϑ a (u.1, u.2.1) E ∧ ip (bits ((u.2.2.1, u.2.2.2).1 ^ E.val)) (bits (u.2.2.1, u.2.2.2).2) = 1 := by sorry
