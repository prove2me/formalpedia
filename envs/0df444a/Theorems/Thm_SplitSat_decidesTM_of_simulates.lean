-- Prove2me | Theorems.Thm_SplitSat_decidesTM_of_simulates
-- name    : SplitSat.decidesTM_of_simulates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:33:32.619455+00:00
-- url     : https://prove2.me/theorems/851b72e9-294d-41a9-afc3-d4baed39fd5e
-- title:
--   Split Sat: decides TM of simulates
-- statement:
--   If Ms decides k-SAT with the exponent δ/2 and the constant c, and the Turing machine M simulates
--   Ms with polynomial overhead, then M decides k-SAT within ⌊C·2^{δn}⌋ steps, for some C ≥ c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L56-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L56-L102

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

theorem SplitSat.decidesTM_of_simulates {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : Decides Ms k (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatK.DecidesTM k M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
