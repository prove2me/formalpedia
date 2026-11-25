-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b
-- name    : P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:40.028874+00:00
-- url     : https://prove2.me/theorems/910fd4b0-72c7-5fe9-b80c-af443367a1ed
-- title:
--   P2 M Companion Theory Rg Exh Hk iso back  c404c772443b: P2 M Companion Theory Rg Exh Hk iso back  c404c772443b
-- statement:
--   The P2 M Companion Theory Rg Exh Hk iso back  c404c772443b construction uses the P2 M Companion Theory Rg Exh Hk iso back  c404c772443b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L70-L76

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}

theorem P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b {Y Y' : GMod n} (hY : Iso Y Y') (z : ℂ)
    (h : ∀ a b, ∀ x ∈ backSub Y z, (tensD Y).E a b x ∈ backSub Y z)
    (h' : ∀ a b, ∀ x ∈ backSub Y' z, (tensD Y').E a b x ∈ backSub Y' z) :
    Iso (back Y z h) (back Y' z h') := by sorry

alias «CompanionTheory».«RgExh».«Hk».«iso_back'» := P2M_CompanionTheory_RgExh_Hk_iso_back__c404c772443b
