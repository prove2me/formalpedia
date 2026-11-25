-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_prodAtlas_holoMap_fst
-- name    : ReciprocityTheory.AnForm.M.prodAtlas_holoMap_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:29.085319+00:00
-- url     : https://prove2.me/theorems/8463242c-b78f-4de7-a87a-de306f0084e0
-- title:
--   M: prod Atlas holo Map fst
-- statement:
--   The M construction uses the prod Atlas holo Map fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L101-L103

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint CompatibleChartOperations
noncomputable section

theorem ReciprocityTheory.AnForm.M.prodAtlas_holoMap_fst {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : HoloMap (prodAtlas A B) A Prod.fst := by sorry
