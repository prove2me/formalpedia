-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_prodChart_holo_snd
-- name    : ReciprocityTheory.AnForm.M.prodChart_holo_snd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:46.604811+00:00
-- url     : https://prove2.me/theorems/19d12720-e12b-51ca-b43c-40841cd10ba8
-- title:
--   M: prod Chart holo snd
-- statement:
--   The M construction uses the prod Chart holo snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L74-L84

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
variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)

theorem ReciprocityTheory.AnForm.M.prodChart_holo_snd (j : Fin A.n) (k : Fin B.n) (l : Fin B.n) :
    AnalyticOnNhd ℂ (B.chart l ∘ Prod.snd ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (Prod.snd ⁻¹' (B.chart l).source)) := by sorry
