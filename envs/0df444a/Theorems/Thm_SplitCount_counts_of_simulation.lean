-- Prove2me | Theorems.Thm_SplitCount_counts_of_simulation
-- name    : SplitCount.counts_of_simulation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:12.428651+00:00
-- url     : https://prove2.me/theorems/66ce10a9-33b9-4c06-b148-172f5a2f9468
-- title:
--   Split Count: counts of simulation
-- statement:
--   If N simulates M with the overhead q·(T+1)·(|x|+S+1)^q, the code of a k-CNF on n variables has
--   length + 1 at most a·(n+2)^d, and M writes the number of satisfying assignments within c·2^{(δ/2)n}
--   steps on states of size at most c·(length + 1)^c, then N counts the satisfying assignments of k-CNFs
--   within ⌊C·2^{δn}⌋ steps, for some C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Host.lean#L35-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Host.lean#L35-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SplitCount_Host
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Turing

theorem SplitCount.counts_of_simulation {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (M : Stepped (List Bool) (List Bool)) (N' : TM2ComputableAux Bool Bool) (q : ℕ)
    (hP : ∀ (x w : List Bool) (T S : ℕ), M.Runs x T S w →
      Nonempty (TM2OutputsInTime N'.tm (x.map N'.inputAlphabet.invFun) (some (w.map N'.outputAlphabet.invFun)) (q * (T + 1) * (x.length + S + 1) ^ q)))
    (c a d : ℕ) (hlen : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ → (SatK.enc k φ).length + 1 ≤ a * (n + 2) ^ d)
    (h : ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
      ∃ T : ℕ, M.Runs (SatK.enc k φ) T (c * ((SatK.enc k φ).length + 1) ^ c) (SatK.binary n (SatK.numSat φ)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n)) :
    ∃ C : ℕ, SatK.CountsTM k N' fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
