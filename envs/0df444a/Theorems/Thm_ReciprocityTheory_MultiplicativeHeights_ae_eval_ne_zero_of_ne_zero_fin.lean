-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_of_ne_zero_fin
-- name    : ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:30.849807+00:00
-- url     : https://prove2.me/theorems/1b850340-d4b9-427f-ad7a-59c2b24d29d1
-- title:
--   Multiplicative Heights: ae eval ne zero of ne zero fin
-- statement:
--   The Multiplicative Heights construction uses the ae eval ne zero of ne zero fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L7-L53

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric

theorem ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by sorry
