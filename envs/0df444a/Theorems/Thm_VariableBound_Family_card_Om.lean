-- Prove2me | Theorems.Thm_VariableBound_Family_card_Om
-- name    : VariableBound.Family.card_Om
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:12.580204+00:00
-- url     : https://prove2.me/theorems/ab2818a0-c682-4f58-8d73-0504c0d52753
-- title:
--   Family: card Om
-- statement:
--   Proof of Lemma 13 (Family of checks): |Ω| ≥ (15/16)·|𝔽|⁴, if 1 ≤ a, a − 1 ≤ s and 1 ≤ m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L144-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L144-L148

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

theorem VariableBound.Family.card_Om (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) :
    15 * Fintype.card F ^ 4 ≤ 16 * #(Om bits ϑ a) := by sorry
