-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredPreparationFields_reads
-- name    : ThreeSum.WeightedGlobalColoredPreparationFields.reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:20:49.674917+00:00
-- url     : https://prove2.me/theorems/d66e5744-1536-4331-a23e-879693db2508
-- title:
--   Weighted Global Colored Preparation Fields: reads
-- statement:
--   The Weighted Global Colored Preparation Fields construction uses the reads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L35-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredPreparationFields.lean#L35-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_LightTernaryColoredInitializationProof
import Definitions.Def_Submission_Weighted_Global_TernaryColoredPreparationFields
import Definitions.Def_WeightedCache3SUM_Alias_96784e4910534891
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixInputs_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_reads
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSeedDataReads_reads

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredPreparationFields
open Light WeightedGlobalConcreteProfile WeightedGlobalColoredLoopSetup LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredPreparationFields.reads {P : Profile κ} {n free menu : ℕ} {A B C : List ℤ} {μ : ℕ→ℤ}
    (H : Seg μ (headerAt free n (LightColorParametersCosts.width n))
      (LightWeightedGlobalColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C)) :
    ∀i<19,μ (headerAt free n (LightColorParametersCosts.width n)+i)=(field P n free menu A B C i:ℤ) := by sorry
