-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_prodChart_holo_fst
-- name    : ReciprocityTheory.AnForm.M.prodChart_holo_fst
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:16.093623+00:00
-- url     : https://prove2.me/theorems/7d98f233-5a30-4205-be49-9524090abadc
-- title:
--   M: prod Chart holo fst
-- statement:
--   The M construction uses the prod Chart holo fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean#L62-L72

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

theorem ReciprocityTheory.AnForm.M.prodChart_holo_fst (j : Fin A.n) (k : Fin B.n) (l : Fin A.n) :
    AnalyticOnNhd ℂ (A.chart l ∘ Prod.fst ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (Prod.fst ⁻¹' (A.chart l).source)) := by sorry
