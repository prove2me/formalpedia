-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_spherePoint
-- name    : ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:00.655912+00:00
-- url     : https://prove2.me/theorems/2caaa0fa-89a5-44f2-ab51-8ddeb26b062e
-- title:
--   Multiplicative Heights: continuous sphere Point
-- statement:
--   The Multiplicative Heights construction uses the continuous sphere Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresA.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/IntCoresA.lean#L9-L11

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
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
open MeasureTheory Metric

theorem ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by sorry
