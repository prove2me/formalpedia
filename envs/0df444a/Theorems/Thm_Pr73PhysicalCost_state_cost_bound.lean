-- Prove2me | Theorems.Thm_Pr73PhysicalCost_state_cost_bound
-- name    : Pr73PhysicalCost.state_cost_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.688206+00:00
-- url     : https://prove2.me/theorems/084c2117-9c8d-402a-bae3-db4d5a75b116
-- title:
--   Pr73PhysicalCost: State cost bound
-- statement:
--   The pinned PR73 actual characteristic is already proved. Every member of every state family obeys this unnormalized bound under uniform physical contracts; the family can contain arbitrarily many volumes and spectators.
--
--   The PR73 conditional physical-cost bound, under explicit implementation and recurrence hypotheses. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73PhysicalCost.lean#L14-L44). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/full-transfer/latest-analytic/Pr73PhysicalCost.lean#L14-L44 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_PhysicalCostTransfer
import Definitions.Def_Pr73ProfileReal
import Definitions.Def_Pr73PhysicalCost
set_option autoImplicit true
open Pr73PhysicalCost
open Pr73ProfileCertificate
open scoped BigOperators

theorem Pr73PhysicalCost.state_cost_bound {S : Type}
    (width : S → ℕ) (volume cost : S → ℝ)
    (child : S → (r : Row) → Fin r.multiplicity → S)
    (B C : ℝ) (hvolume : ∀ s, 0 ≤ volume s)
    (child_width : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      width (child s r j) = r.width * (width s / m))
    (child_volume : ∀ s, m ≤ width s → ∀ r ∈ rows, ∀ j,
      volume (child s r j) = volume s / W)
    (uniform_base : ∀ s, 0 < width s → width s < m → cost s ≤ B * volume s)
    (physical_recurrence : ∀ s, m ≤ width s → cost s ≤ C * volume s +
      (rows.map (fun r => ∑ j : Fin r.multiplicity, cost (child s r j))).sum) :
    ∀ s, 0 < width s → cost s ≤ costConstant B C * volume s *
      (width s : ℝ) ^ (1 - (saving : ℝ)) := by sorry
