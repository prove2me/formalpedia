-- Prove2me | Theorems.Thm_ThmVariables_conclusion_of_cut
-- name    : ThmVariables.conclusion_of_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:30:18.302162+00:00
-- url     : https://prove2.me/theorems/76ed5604-085e-4d24-917d-0dce17492736
-- title:
--   Thm Variables: conclusion of cut
-- statement:
--   A machine with the bound of Theorem D (a) for a solver whose levels are K_ℓ and e′_ℓ, the number
--   in [e_ℓ, 2e_ℓ] cut at 1, has the bound for K_ℓ and e_ℓ with twice the constant. Hypotheses: K, e, C₀
--   satisfy the printed inequalities (`CliqueLevels.Levels`), `num` returns a number in [e_ℓ, 2e_ℓ]
--   (`CliqueLevels.NumberBetween`), Q is a sequence of levels of the solver S for the numbers e′_ℓ, and
--   S has K_ℓ at the ℓ-th index of Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L65-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/ThmVariables/PartA.lean#L65-L76

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

theorem ThmVariables.conclusion_of_cut {Idx : Type} [Enc Idx] {S : Solver Idx} {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ C₀' : ℕ} {num : List Unit × List Unit → ℕ × ℕ} (Q : S.Seq (cutNumber K num) C₀')
    (hL : Levels K e C₀) (hnum : CliqueLevels.NumberBetween K e num) (hK : ∀ l : ℕ, S.K (Q.idx l) = K l) {M : TM2ComputableAux Bool Bool} {C' : ℕ} (hM : ThmVariablesAFor S Q M C') :
    Conclusion K e M (2 * C') := by sorry
