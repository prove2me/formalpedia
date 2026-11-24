-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_joinForm_b4deacf8f20d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_joinForm_b4deacf8f20d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:53.843301+00:00
-- url     : https://prove2.me/theorems/027772ae-9a6e-4f8f-bc16-fd80711be056
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog join Form b4deacf8f20d: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog join Form b4deacf8f20d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog join Form b4deacf8f20d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog join Form b4deacf8f20d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L37-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PVerticalDivisorJoinPullback.lean#L37-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
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
noncomputable section
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_joinForm_b4deacf8f20d [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomog_joinForm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_joinForm_b4deacf8f20d
