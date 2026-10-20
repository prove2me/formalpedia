-- Prove2me | Theorems.Thm_SoficGroups_KunGuardedCanonicalMatchedDensity_canonical_matched_density_of_guarded
-- name    : SoficGroups.KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/4c2379b7-8372-4ba3-a3d0-93988c0b81d1
-- title:
--   SoficGroups.KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGuardedCanonicalMatchedDensity
open Filter Topology

theorem SoficGroups.KunGuardedCanonicalMatchedDensity.canonical_matched_density_of_guarded
    (V : ℕ → Type*) [∀ n, DecidableEq (V n)]
    (U : (n : ℕ) → Finset (V n))
    (P : (n : ℕ) → Finpartition (U n))
    {ι : Type*} (I : ℕ → Finset ι)
    (w : (n : ℕ) → ι → Equiv.Perm (V n))
    (B E C : (n : ℕ) → Finset (V n))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n ∪ E n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (P n) (I n) (w n) (B n)).card : ℝ) /
            (C n).card))
      atTop (nhds 0) := by sorry
