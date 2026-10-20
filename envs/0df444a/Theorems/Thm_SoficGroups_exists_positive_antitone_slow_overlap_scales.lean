-- Prove2me | Theorems.Thm_SoficGroups_exists_positive_antitone_slow_overlap_scales
-- name    : SoficGroups.exists_positive_antitone_slow_overlap_scales
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/0f8026cd-d578-4cbc-a2ea-60301f65843a
-- title:
--   SoficGroups.exists_positive_antitone_slow_overlap_scales
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.exists_positive_antitone_slow_overlap_scales
    (e : ℕ → ℝ) (he_nonneg : ∀ n, 0 ≤ e n)
    (he : Tendsto e atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧ Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧ Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => e n / eta n) atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) := by sorry
