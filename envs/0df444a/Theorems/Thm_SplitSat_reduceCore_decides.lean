-- Prove2me | Theorems.Thm_SplitSat_reduceCore_decides
-- name    : SplitSat.reduceCore_decides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:24.086046+00:00
-- url     : https://prove2.me/theorems/31687d20-a392-45a1-aa44-67b6a0c1bd33
-- title:
--   Split Sat: reduce Core decides
-- statement:
--   **The reduction is correct and fast, for every procedure D and every tree.** Let k ≥ 3 and δ >
--   0; let `step`, from the root `rootP`, sparsify width k with at most 2^{δn/3} leaves of at most B·n
--   clauses; let D decide 3-SAT with an exponent δ₃ ≥ 0 such that δ₃·(1 + (k−3)·B) ≤ δ/3. Then
--   `reduceCore step D` decides k-SAT with the exponent δ, in the sense of `DecidesW k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Walk.lean#L35-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Walk.lean#L35-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Mathlib.Tactic
import Definitions.Def_SplitSat_Walk
import Theorems.Thm_WidthK_InvK_step

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width

theorem SplitSat.reduceCore_decides {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {step : Fml → Option (Fml × Fml)} {Dd B Sk : ℕ}
    (hsp : Sparsifies k (δ / 3) step rootP Dd B Sk) (D : StepMachine (List Unit × Fml) Bool) {δ₃ : ℝ} {c : ℕ} (h0 : 0 ≤ δ₃)
    (hδB : δ₃ * (1 + ((k : ℝ) - 3) * B) ≤ δ / 3) (hD : Decides3 D δ₃ c) : ∃ c' : ℕ, DecidesW k (reduceCore step D) δ c' := by sorry
