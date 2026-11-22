-- Prove2me | Theorems.Thm_Scales
-- name    : Scales
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:37:26.542096+00:00
-- url     : https://prove2.me/theorems/1daa1a1e-83b2-4655-b8b9-67ae61cb1421
-- title:
--   Scales: Scales
-- statement:
--   The paper's `lem:scales`.  There are a threshold `δ > 0` and a finite nonempty set
--   of radii in `(0, 1/4)`, depending only on `p`, `k` and `β`, such that every
--   `p`-harmonic `v` on `ball 0 1` normalized by `|v| ≤ 1`, `v 0 = 0` and
--   `‖gradient v 0‖ ≤ δ` already satisfies the strict decay `|v| < ρ ^ (k + β)` on
--   `ball 0 ρ` for one of those radii.
--
--   Note the quantifier order: `δ` and the radii are produced BEFORE `v`, which is the
--   whole content — they are uniform over the normalized family.  This is what converts
--   the qualitative, solution-dependent regularity into something quantitative.  The
--   radii are returned as a finite nonempty set so that a consumer can form their
--   minimum, which is what the iteration of the main proof needs.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Scales.lean#L17-L175
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/Scales.lean#L17-L175

import Definitions.Def_PHigherOrder_CriticalMemberDecay
import Definitions.Def_PHigherOrder_CompactJetFamilyCompact
import Definitions.Def_PHigherOrder_UniformDelta
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_Scales
import Theorems.Thm_CompactJetFamilyCompact
import Theorems.Thm_CriticalMemberDecay
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_UniformDelta

set_option autoImplicit false

theorem Scales (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : Finset ℝ, R.Nonempty ∧ (∀ ρ ∈ R, 0 < ρ ∧ ρ < 1 / 4) ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        ‖gradient v 0‖ ≤ δ →
        ∃ ρ ∈ R, ∀ y : Plane, ‖y‖ < ρ → |v y| < ρ ^ ((k : ℝ) + β) := by sorry
