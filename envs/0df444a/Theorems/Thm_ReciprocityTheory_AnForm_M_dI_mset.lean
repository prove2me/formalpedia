-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_dI_mset
-- name    : ReciprocityTheory.AnForm.M.dI_mset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:12.050276+00:00
-- url     : https://prove2.me/theorems/780f9881-174c-4e64-b11c-5771b0c5b473
-- title:
--   M: d I mset
-- statement:
--   The M construction uses the d I mset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L168-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean#L168-L177

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

theorem ReciprocityTheory.AnForm.M.dI_mset {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {s : Set Z} (hs : MeasurableSet s) :
    MeasurableSet (φ.target ∩ φ.symm ⁻¹' s) := by sorry
