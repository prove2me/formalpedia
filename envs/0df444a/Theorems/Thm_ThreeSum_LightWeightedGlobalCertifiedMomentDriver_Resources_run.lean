-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_Resources_run
-- name    : ThreeSum.LightWeightedGlobalCertifiedMomentDriver.Resources.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:53:05.824053+00:00
-- url     : https://prove2.me/theorems/d72fd961-898a-4ab3-bb4c-975aea5c3d54
-- title:
--   Resources: run
-- statement:
--   The Resources construction uses the run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDriverResources.lean#L48-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentDriverResources.lean#L48-L64

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDriverResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalCertifiedMomentDriver
open Light TernaryMomentSchedule LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.LightWeightedGlobalCertifiedMomentDriver.Resources.run {N d originalB originalC matrix terms a b U W : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Limits}
    {μ : ℕ→ℤ} {B C : ℕ→ℤ}
    (H : Resources S lim d originalB originalC matrix terms a b U W μ B C) :
    Meets lim (program S terms) (139*(channels terms).length+1) d
      (LightWeightedGlobalMomentChannelFactory.args S originalB originalC matrix) μ (time S terms)
      (fun _ ν => (∀ k<terms, ∀ i<S.front.count,
        ν (matrix+k*S.front.count+i)=∑ p : WeightedGlobalNativePairMoments.Pair S i,
          WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode B C p^k) ∧
        Kept μ ν matrix) := by sorry
