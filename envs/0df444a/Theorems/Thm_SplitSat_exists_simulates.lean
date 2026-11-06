-- Prove2me | Theorems.Thm_SplitSat_exists_simulates
-- name    : SplitSat.exists_simulates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:34:20.4509+00:00
-- url     : https://prove2.me/theorems/2beab49d-c625-4373-9c20-690b6547eada
-- title:
--   Split Sat: exists simulates
-- statement:
--   A machine cut into polynomial-time steps, from words to a bit, is simulated with polynomial
--   overhead by a Turing machine of Mathlib with finite alphabets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L47-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L47-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_SplitSat_Simulate
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping

theorem SplitSat.exists_simulates (Ms : StepMachine (List Bool) Bool) (hp : PolyTimeSteps Ms) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M Ms q := by sorry
