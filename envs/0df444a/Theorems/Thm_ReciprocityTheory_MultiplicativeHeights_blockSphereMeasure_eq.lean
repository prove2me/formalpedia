-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockSphereMeasure_eq
-- name    : ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:37.067108+00:00
-- url     : https://prove2.me/theorems/02878db3-b112-4b76-9212-89cd09644acf
-- title:
--   Multiplicative Heights: block Sphere Measure eq
-- statement:
--   The Multiplicative Heights construction uses the block Sphere Measure eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L210-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean#L210-L217

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

theorem ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_eq (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by sorry
