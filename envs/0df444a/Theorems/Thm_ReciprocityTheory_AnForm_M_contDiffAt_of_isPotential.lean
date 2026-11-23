-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_contDiffAt_of_isPotential
-- name    : ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:41.188301+00:00
-- url     : https://prove2.me/theorems/c0310670-7882-4b92-84ff-b50c968eb23e
-- title:
--   M: cont Diff At of is Potential
-- statement:
--   The M construction uses the cont Diff At of is Potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L33-L37

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ ∞ (P.φ x ∘ (A.chart j).symm) y := by sorry
