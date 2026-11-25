-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sum_log_normSq
-- name    : ReciprocityTheory.MultiplicativeHeights.sum_log_normSq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:17.278837+00:00
-- url     : https://prove2.me/theorems/eb8e8934-997f-485a-a819-320739eecf2f
-- title:
--   Multiplicative Heights: sum log norm Sq
-- statement:
--   The Multiplicative Heights construction uses the sum log norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L97-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegBA.lean#L97-L115

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.sum_log_normSq {K : Type} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log (Complex.normSq (σ x)) =
      2 * Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by sorry
