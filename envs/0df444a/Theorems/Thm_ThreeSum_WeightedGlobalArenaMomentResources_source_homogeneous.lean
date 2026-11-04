-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaMomentResources_source_homogeneous
-- name    : ThreeSum.WeightedGlobalArenaMomentResources.source_homogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:44:08.352969+00:00
-- url     : https://prove2.me/theorems/34b001cd-60b1-44f5-9e89-d2d2767d502d
-- title:
--   Weighted Global Arena Moment Resources: source homogeneous
-- statement:
--   The Weighted Global Arena Moment Resources construction uses the source homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L36-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaMomentResources.lean#L36-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_TernaryArenaReporterBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaMomentResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaMomentResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaPairMass
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeMomentBounds
open WeightedGlobalMomentWeightBounds
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaMomentResources.source_homogeneous (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    ∀ pair∈(source (r := r) maps cap I right).records,
      WeightedGlobalBank.rank ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key pair.2))=r*alphaRank m := by sorry
