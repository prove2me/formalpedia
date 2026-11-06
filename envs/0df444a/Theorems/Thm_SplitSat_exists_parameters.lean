-- Prove2me | Theorems.Thm_SplitSat_exists_parameters
-- name    : SplitSat.exists_parameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:22.362094+00:00
-- url     : https://prove2.me/theorems/63227598-fc90-4296-97d9-5706bfc79a19
-- title:
--   Split Sat: exists parameters
-- statement:
--   For every k ≥ 3 and δ > 0 there are a threshold parameter τ and an exponent δ₃ > 0 such that,
--   for every procedure D with polynomial-time steps that decides 3-SAT with the exponent δ₃,
--   `REDUCE k τ D` has polynomial-time steps and decides k-SAT with the exponent δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L57-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L57-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal

theorem SplitSat.exists_parameters (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) : ∃ (τ : ℕ) (δ₃ : ℝ), 0 < δ₃ ∧
    ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), PolyTimeSteps D → Decides3 D δ₃ c →
      PolyTimeSteps (REDUCE k τ D) ∧ ∃ c' : ℕ, Decides (REDUCE k τ D) k δ c' := by sorry
