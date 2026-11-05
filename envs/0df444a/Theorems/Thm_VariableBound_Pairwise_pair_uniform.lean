-- Prove2me | Theorems.Thm_VariableBound_Pairwise_pair_uniform
-- name    : VariableBound.Pairwise.pair_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:31:47.801511+00:00
-- url     : https://prove2.me/theorems/5effee76-450e-4ba2-918a-b17eca747e58
-- title:
--   Pairwise: pair uniform
-- statement:
--   Proof of Lemma 13 (Family of checks): for distinct ϑ, ϑ' ∈ 𝔽 the pair (u₁ϑ + u₂, u₁ϑ' + u₂) is
--   uniformly distributed in 𝔽² when (u₁, u₂) is: the map is a bijection of 𝔽².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L75-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/Pairwise.lean#L75-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise
set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F] [Algebra (ZMod 2) F]

theorem VariableBound.Pairwise.pair_uniform (θ θ' : F) (h : θ ≠ θ') : Function.Bijective fun p : F × F => (p.1 * θ + p.2, p.1 * θ' + p.2) := by sorry
