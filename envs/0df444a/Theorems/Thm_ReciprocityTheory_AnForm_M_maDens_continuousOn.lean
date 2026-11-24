-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_continuousOn
-- name    : ReciprocityTheory.AnForm.M.maDens_continuousOn
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:06.293344+00:00
-- url     : https://prove2.me/theorems/78912b81-d679-472e-b556-fc3f88969de5
-- title:
--   M: ma Dens continuous On
-- statement:
--   The M construction uses the ma Dens continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L84-L90

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
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
open scoped ContDiff ComplexOrder Matrix
noncomputable section

theorem ReciprocityTheory.AnForm.M.maDens_continuousOn {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ))
    (hV : IsOpen V) (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) V) : ContinuousOn (maDens φ) V := by sorry
