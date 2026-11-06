-- Prove2me | Theorems.Thm_Printed_level_one_of
-- name    : Printed.level_one_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:32:39.959316+00:00
-- url     : https://prove2.me/theorems/4cd843eb-6478-4cbe-a7e3-ee6c7c5504ef
-- title:
--   Printed: level one of
-- statement:
--   «Apply Lemma 1 to the network with the smaller total»: the run for one ι. The bound of Lemma 1
--   (`StOnProcedures`) on the row network or the column network, and the display on the smaller total
--   (`stMin`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L124-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/LevelCost.lean#L124-L196

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

theorem Printed.level_one_of (hO : StOnProcedures) {K g C₁ a : ℕ} {e : ℝ} {NM : NetMachine} (h0 : 0 ≤ e) (hg1 : 1 ≤ g) (hNM : ComputesNetworks NM C₁ g K e)
    {c : List Unit × List Unit} {lam B S y : ℕ} {O : TableQuery → Option ℤ} {Rm : Inst (Fin (g * g)) (List Bool)} (hcl : c.1.length = lam) (hl : 1 ≤ lam)
    (hnet : ∀ tr, SecNetworks.IsNetwork ((gridProcs g tr).close O) (c, y) (levelNetP g tr lam y Rm) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a) S) :
    ∃ τ : ℕ, (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O))).Runs (c, y) τ
        (size (c, y) + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ + S + 4 + 1) (Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y)) ∧
      (τ : ℝ) + 1 ≤ (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ) := by sorry
