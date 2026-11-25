-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:29.487156+00:00
-- url     : https://prove2.me/theorems/1a3554ad-298b-4645-81c3-868e016bbdfa
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm prod le one 2cd74388c558: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm prod le one 2cd74388c558
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm prod le one 2cd74388c558 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm prod le one 2cd74388c558 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L56-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558 {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L)
    (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ 1) :
    gaussNormOf (normAbv L) (∏ b ∈ s, f b) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_prod_le_one» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_prod_le_one_2cd74388c558
