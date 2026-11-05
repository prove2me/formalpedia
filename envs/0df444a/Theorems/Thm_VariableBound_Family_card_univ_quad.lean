-- Prove2me | Theorems.Thm_VariableBound_Family_card_univ_quad
-- name    : VariableBound.Family.card_univ_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:35:49.256705+00:00
-- url     : https://prove2.me/theorems/ca3fc272-56cd-4b6b-8b67-131aa4105281
-- title:
--   Family: card univ quad
-- statement:
--   𝔽⁴ has |𝔽|⁴ elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Main.lean#L50-L52

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

theorem VariableBound.Family.card_univ_quad : #(univ : Finset (F × F × F × F)) = Fintype.card F ^ 4 := by sorry
