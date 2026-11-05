-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalCertifiedMomentDriver_Resources_run
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalCertifiedMomentDriver.Resources.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:29:28.695909+00:00
-- url     : https://prove2.me/theorems/2388b11d-7196-48b3-8496-4a71530adb92
-- title:
--   run
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDriverResources.lean#L48-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentDriverResources.lean#L48-L64

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryCertifiedMomentDriver
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDriverResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalCertifiedMomentDriver
open Light TernaryMomentSchedule LightWeightedGlobalMomentChannelFactory

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalCertifiedMomentDriver.Resources.run {N d originalB originalC matrix terms a b U W : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Limits}
    {μ : ℕ→ℤ} {B C : ℕ→ℤ}
    (H : Resources S lim d originalB originalC matrix terms a b U W μ B C) :
    Meets lim (program S terms) (139*(channels terms).length+1) d
      (LightWeightedGlobalMomentChannelFactory.args S originalB originalC matrix) μ (time S terms)
      (fun _ ν => (∀ k<terms, ∀ i<S.front.count,
        ν (matrix+k*S.front.count+i)=∑ p : WeightedGlobalNativePairMoments.Pair S i,
          WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode B C p^k) ∧
        Kept μ ν matrix) := by sorry
