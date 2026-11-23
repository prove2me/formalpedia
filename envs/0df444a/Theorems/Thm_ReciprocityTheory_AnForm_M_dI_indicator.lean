-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_indicator
-- name    : ReciprocityTheory.AnForm.M.dI_indicator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:19.572543+00:00
-- url     : https://prove2.me/theorems/870dcf92-59e5-44e5-915e-8c120f37d434
-- title:
--   M: d I indicator
-- statement:
--   The M construction uses the d I indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L179-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L179-L189

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.dI_indicator {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {E : Set Z} (hE : MeasurableSet E) (g : Z → ℝ)
    (w : (Fin e → ℂ) → ℝ) (hint : IntegrableOn (fun z => g (φ.symm z) * w z) φ.target) :
    IntegrableOn (fun z => E.indicator g (φ.symm z) * w z) φ.target := by sorry
