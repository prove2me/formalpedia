-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:35.010479+00:00
-- url     : https://prove2.me/theorems/1ec71f9c-1ced-4f31-b8ee-6b36d19cc257
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class Num rename e13bf3796dec: P2 M Ground Theory Heights  Heights Numbers DVR class Num rename e13bf3796dec
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class Num rename e13bf3796dec construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class Num rename e13bf3796dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSubQuotient.lean#L16-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec {σ τ : Type*} (e : σ → τ) (he : Function.Injective e) (cls : τ → K → ℤ)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classNum_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec
