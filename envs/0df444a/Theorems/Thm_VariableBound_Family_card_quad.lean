-- Prove2me | Theorems.Thm_VariableBound_Family_card_quad
-- name    : VariableBound.Family.card_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:08:51.082363+00:00
-- url     : https://prove2.me/theorems/5744de58-7d61-49e9-8fbf-154be0d5adb5
-- title:
--   Family: card quad
-- statement:
--   Proof of Lemma 13 (Family of checks): (u₃, u₄) is independent of (u₁, u₂). The quadruples u with
--   a property of the two pairs are counted pair by pair.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L41-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L41-L46

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
omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F]

theorem VariableBound.Family.card_quad (R : F × F → F × F → Prop) [∀ p r, Decidable (R p r)] :
    #{u : F × F × F × F | R (u.1, u.2.1) (u.2.2.1, u.2.2.2)} = ∑ p : F × F, #{r : F × F | R p r} := by sorry
