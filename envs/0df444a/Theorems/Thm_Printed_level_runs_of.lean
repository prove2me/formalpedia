-- Prove2me | Theorems.Thm_Printed_level_runs_of
-- name    : Printed.level_runs_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:31:26.057662+00:00
-- url     : https://prove2.me/theorems/9759c214-2e97-44c8-945c-80cb8fdf3db6
-- title:
--   Printed: level runs of
-- statement:
--   The paragraph «Cost» for the step machine that `levelMachine` becomes when the tables are built
--   in: value, number of steps, sizes. c holds λ and B in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L202-L348
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L202-L348

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

theorem Printed.level_runs_of (hA : StAskServes) (hO : StOnProcedures) {K g C₁ : ℕ} {e : ℝ} {NM : NetMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hNM : ComputesNetworks NM C₁ g K e) :
    ∃ Cc' : ℕ, ∀ (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ), c.1.length = lam → c.2.length = B → 1 ≤ lam → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) →
      ∃ T : ℕ, (Stepped.bind (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
            (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close (tables (g * g) lam W))) (networkOnSteps g NM ((gridProcs g true).close (tables (g * g) lam W)))))
          (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ))).Runs c T (Cc' * (B + lam) ^ Cc') (Inst.ZW lam [] (listTables (g * g) W)) ∧
        (T : ℝ) ≤ Cc' * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc' := by sorry
