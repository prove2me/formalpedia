-- Prove2me | Theorems.Thm_ThmVariables_numberBetween_cut
-- name    : ThmVariables.numberBetween_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:38:26.087473+00:00
-- url     : https://prove2.me/theorems/f19966f8-b2d5-4ded-a076-753a7a300c64
-- title:
--   Thm Variables: number Between cut
-- statement:
--   A number in [e′_ℓ, 2e′_ℓ] can be computed from ℓ in time polynomial in K_ℓ, for e′_ℓ the number
--   that `num` returns, cut at 1: it is e′_ℓ itself. Hypotheses: Q is a sequence of levels of a solver S
--   for the numbers e′_ℓ, `num` is polynomial-time, and S has K_ℓ at the ℓ-th index of Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L50-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L50-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ThmVariables_PartA
set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)

theorem ThmVariables.numberBetween_cut {Idx : Type} [Enc Idx] {S : Solver Idx} {K : ℕ → ℕ} {num : List Unit × List Unit → ℕ × ℕ} {C₀ : ℕ} (Q : S.Seq (cutNumber K num) C₀)
    (hnum : PolyT num) (hK : ∀ l : ℕ, S.K (Q.idx l) = K l) : PairsToBound.NumberBetween S Q (cutFraction num) := by sorry
