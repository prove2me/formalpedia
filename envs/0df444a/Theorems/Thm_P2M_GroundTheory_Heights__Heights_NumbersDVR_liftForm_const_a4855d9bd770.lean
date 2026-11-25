-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_const_a4855d9bd770
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_const_a4855d9bd770
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:25.820823+00:00
-- url     : https://prove2.me/theorems/d1f490f3-d020-4a47-b532-c1379ad28da2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lift Form const a4855d9bd770: P2 M Ground Theory Heights  Heights Numbers DVR lift Form const a4855d9bd770
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lift Form const a4855d9bd770 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lift Form const a4855d9bd770 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocalizedQuotientIsSimpleModuleOfMul.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LocalizedQuotientIsSimpleModuleOfMul.lean#L80-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul
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
universe u
set_option linter.unusedSectionVars false
variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_const_a4855d9bd770 (a : O) : liftForm (J := J) (C a : MRing ι O) = C a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«liftForm_const» := P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_const_a4855d9bd770
