-- Prove2me | Theorems.Thm_Printed_cost_of_bound
-- name    : Printed.cost_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:48.237605+00:00
-- url     : https://prove2.me/theorems/63db6490-5d34-4846-aced-f83c15bbc45a
-- title:
--   Printed: cost of bound
-- statement:
--   **Section 6, «Cost».** «So … Z is computed in time O(2^{δ'm})», and «Z is the number of
--   assignments of the variables occurring in Φ that satisfy Φ», for any step machine Mc that returns
--   the value of the network of Φ within the bound of Lemma 1 with e = δ'/12 and K ≥ 72/δ'. The
--   sentences of the paper in their order: what Z is (`Eight.network_value_eq`); U < 6m
--   (`Eight.network_total_lt`) and gP ≤ 6(m + g); the exponent (`Eight.network_exponent_lt'`); the
--   remaining factor (`Eight.remaining_factor`). The case m = 0 is run through as well (then U = 0, P = 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L108-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Count.lean#L108-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines

theorem Printed.cost_of_bound {g K : ℕ} {δ' : ℝ} {Mc : Stepped Fml ℤ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      Mc.Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * 3) + 10 + C₁ * (size Φ + satPf g 3 Φ + 1) ^ C₁) (wordNet g 3 Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (δ' / 12 * ((wordNet g 3 Φ).U : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * (satPf g 3 Φ : ℝ)) / K) * ((satPf g 3 Φ : ℝ) + 1) ^ C₁) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by sorry
