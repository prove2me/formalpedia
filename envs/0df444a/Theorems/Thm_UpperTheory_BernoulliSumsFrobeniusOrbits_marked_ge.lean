-- Prove2me | Theorems.Thm_UpperTheory_BernoulliSumsFrobeniusOrbits_marked_ge
-- name    : UpperTheory.BernoulliSumsFrobeniusOrbits.marked_ge
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:38.856867+00:00
-- url     : https://prove2.me/theorems/ae343a15-058c-5ec6-ad76-65c3c398d1b3
-- title:
--   Bernoulli Sums Frobenius Orbits: marked ge
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the marked ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/MarkedGe.lean#L98-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/MarkedGe.lean#L98-L185

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_expectationSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedGe
import Theorems.Thm_GlobalTheory_RandomTops_marked_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.marked_ge :
    ∀ (p : ℕ → ℝ) (δ : ℝ) (r u s : ℕ), (∀ a, 3 / 4 * δ ≤ p a ∧ p a ≤ δ) → 0 ≤ δ → δ ≤ 1 →
      markedLow δ r u ≤ exP p (Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u))) (fun T => ind (Marked T r u s)) := by sorry
