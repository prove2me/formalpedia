-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothOn
-- name    : ReciprocityTheory.AnForm.M.potSmoothOn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:35.973386+00:00
-- url     : https://prove2.me/theorems/7f6282e3-e1d9-5719-b092-6638dc883159
-- title:
--   M: pot Smooth On
-- statement:
--   The M construction uses the pot Smooth On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/LocDens.lean#L35-L38

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

theorem ReciprocityTheory.AnForm.M.potSmoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) :
    ContDiffOn ℝ 2 (P.φ x ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by sorry
