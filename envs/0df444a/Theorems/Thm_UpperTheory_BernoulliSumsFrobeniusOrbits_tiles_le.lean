-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_tiles_le
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.tiles_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:00.704104+00:00
-- url     : https://prove2.me/theorems/eec8cc3d-e6f2-55eb-8d44-a8e6bcd10d43
-- title:
--   Bernoulli Sums Frobenius Orbits: tiles le
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the tiles le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/TilesLe.lean#L26-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/TilesLe.lean#L26-L105

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_TilesLe
import Theorems.Thm_GlobalTheory_RandomTops_marked_congr
import Theorems.Thm_GlobalTheory_RandomTops_tile_disjoint
import Theorems.Thm_GlobalTheory_RandomTops_tiles_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
open GlobalTheory.RandomTops (tile tile_disjoint marked_congr)

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.tiles_le :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (n r u M₀ i₀ : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 → 1 ≤ u →
      (M₀ + 1) * ((6 * r + 1) * u) ≤ n →
      exP p ((range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤ n * (1 - markedLow δ r u) ^ M₀ := by sorry
