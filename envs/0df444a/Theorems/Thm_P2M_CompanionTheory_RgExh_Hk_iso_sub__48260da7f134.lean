-- Prove2me | Theorems.Thm_P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134
-- name    : P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:46.551347+00:00
-- url     : https://prove2.me/theorems/9c01bef1-5357-5c34-b38f-80c7bb748603
-- title:
--   P2 M Companion Theory Rg Exh Hk iso sub  48260da7f134: P2 M Companion Theory Rg Exh Hk iso sub  48260da7f134
-- statement:
--   The P2 M Companion Theory Rg Exh Hk iso sub  48260da7f134 construction uses the P2 M Companion Theory Rg Exh Hk iso sub  48260da7f134 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L48-L52

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

theorem P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134 {X X' : GMod n} (φ : X.V ≃ₗ[ℂ] X'.V) (hφ : ∀ a b x, φ (X.E a b x) = X'.E a b (φ x))
    (S : Submodule ℂ X.V) (S' : Submodule ℂ X'.V) (hS : S.map (φ : X.V →ₗ[ℂ] X'.V) = S')
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (h' : ∀ a b, ∀ x ∈ S', X'.E a b x ∈ S') :
    Iso (X.sub S h) (X'.sub S' h') := by sorry

alias «CompanionTheory».«RgExh».«Hk».«iso_sub'» := P2M_CompanionTheory_RgExh_Hk_iso_sub__48260da7f134
