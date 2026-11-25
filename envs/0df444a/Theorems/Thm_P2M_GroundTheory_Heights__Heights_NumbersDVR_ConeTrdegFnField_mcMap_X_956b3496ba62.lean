-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mcMap_X_956b3496ba62
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mcMap_X_956b3496ba62
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:02.810291+00:00
-- url     : https://prove2.me/theorems/64681c24-d51b-564f-86f6-593126fff00a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mc Map X 956b3496ba62: P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mc Map X 956b3496ba62
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mc Map X 956b3496ba62 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mc Map X 956b3496ba62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L56-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mcMap_X_956b3496ba62 (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) :
    mcMap O y (X p) = C (y p) * X p.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ConeTrdegFnField».«mcMap_X» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mcMap_X_956b3496ba62
