-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_st_byPartsSymm_of
-- name    : ReciprocityTheory.AnForm.M.st_byPartsSymm_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:52.463579+00:00
-- url     : https://prove2.me/theorems/582d9c99-fbed-455c-8598-e31075f3d414
-- title:
--   M: st by Parts Symm of
-- statement:
--   The M construction uses the st by Parts Symm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L308-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesC.lean#L308-L322

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem ReciprocityTheory.AnForm.M.st_byPartsSymm_of (hP : ReciprocityTheory.AnForm.A.PartsStatement) : ByPartsSymmStatement := by sorry
