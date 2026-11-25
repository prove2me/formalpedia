-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_hecke_of__b333356e2fe6
-- name    : P2M_CompanionTheory_RgExh_Hk_hecke_of__b333356e2fe6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:20.149357+00:00
-- url     : https://prove2.me/theorems/f003ebb6-ea0d-5ccb-8213-da3f22223ac9
-- title:
--   P2 M Companion Theory Rg Exh Hk hecke of  b333356e2fe6: P2 M Companion Theory Rg Exh Hk hecke of  b333356e2fe6
-- statement:
--   The P2 M Companion Theory Rg Exh Hk hecke of  b333356e2fe6 construction uses the P2 M Companion Theory Rg Exh Hk hecke of  b333356e2fe6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/ScalarCharacters/ScalCharOfSimple.lean#L106-L112

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_ScalarCharacters_ScalCharOfSimple
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
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}

theorem P2M_CompanionTheory_RgExh_Hk_hecke_of__b333356e2fe6 (hQ : QdetEq) (hC : StepChar) (_hCH : CayleyHam) (hV : NonVan) (hNS : NonScal) (hB : Back)
    (hOS : OmScal) (hF : FwdSimple) (hR : Reflect) : Hecke := by sorry

alias «CompanionTheory».«RgExh».«Hk».«hecke_of'» := P2M_CompanionTheory_RgExh_Hk_hecke_of__b333356e2fe6
