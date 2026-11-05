-- Prove2me | Theorems.Thm_P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce
-- name    : P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:27.482789+00:00
-- url     : https://prove2.me/theorems/45f2f47a-6e03-46cf-8a9b-039f8a2b99e1
-- title:
--   P2 M Clause Bound Parity Checks Step One sum powerset neg one  f4c3a51312ce: P2 M Clause Bound Parity Checks Step One sum powerset neg one  f4c3a51312ce
-- statement:
--   The sum of (−1)^|s| over the subsets s of a set that is not empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L83-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L83-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks

theorem P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce {E : Type} [DecidableEq E] {A : Finset E} (hA : A ≠ ∅) : ∑ s ∈ A.powerset, (-1 : ℤ) ^ #s = 0 := by sorry

alias «ClauseBound».«ParityChecks».«StepOne».«sum_powerset_neg_one'» := P2M_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_one__f4c3a51312ce
