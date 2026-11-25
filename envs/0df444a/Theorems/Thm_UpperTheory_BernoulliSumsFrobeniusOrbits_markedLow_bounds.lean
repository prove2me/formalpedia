-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_markedLow_bounds
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.markedLow_bounds
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:56.810167+00:00
-- url     : https://prove2.me/theorems/8ed54bb1-938a-5eec-87de-f7550b235f3d
-- title:
--   Bernoulli Sums Frobenius Orbits: marked Low bounds
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the marked Low bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/MarkedLowBounds.lean#L6-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/MarkedLowBounds.lean#L6-L95

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLowBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.markedLow_bounds :
    ∀ (δ : ℝ) (r : ℕ), 0 < δ → δ ≤ 1 / 100 →
      (1 / 10 : ℝ) ^ (6 * r + 1) ≤ markedLow δ r (Formalism.MainNotions.G.goodU δ) ∧ markedLow δ r (Formalism.MainNotions.G.goodU δ) ≤ 1 := by sorry
