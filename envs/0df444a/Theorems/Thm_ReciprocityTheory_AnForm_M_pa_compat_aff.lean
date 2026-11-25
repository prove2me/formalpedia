-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_pa_compat_aff
-- name    : ReciprocityTheory.AnForm.M.pa_compat_aff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:32.201864+00:00
-- url     : https://prove2.me/theorems/db4cb18a-5300-4ea8-80ed-479039970497
-- title:
--   M: pa compat aff
-- statement:
--   The M construction uses the pa compat aff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Partition.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/Partition.lean#L42-L50

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.M.pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by sorry
