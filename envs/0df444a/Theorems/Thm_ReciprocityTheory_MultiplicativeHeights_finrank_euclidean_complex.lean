-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finrank_euclidean_complex
-- name    : ReciprocityTheory.MultiplicativeHeights.finrank_euclidean_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:25.747713+00:00
-- url     : https://prove2.me/theorems/40d3c82c-1222-4bd2-9abc-8274ab8b2a7f
-- title:
--   Multiplicative Heights: finrank euclidean complex
-- statement:
--   The Multiplicative Heights construction uses the finrank euclidean complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SJCoreB.lean#L29-L32

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
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
open MeasureTheory Metric Set Real

theorem ReciprocityTheory.MultiplicativeHeights.finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by sorry
