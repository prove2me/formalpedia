-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_isMultiHomog_rename_9ca82d06f080
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_isMultiHomog_rename_9ca82d06f080
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:04.555614+00:00
-- url     : https://prove2.me/theorems/0e81acc0-eb68-4d10-915f-745ae441ec2f
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor is Multi Homog rename 9ca82d06f080: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor is Multi Hom
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor is Multi Homog rename 9ca82d06f080 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor is Multi Homog rename 9ca82d06f080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L26-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_isMultiHomog_rename_9ca82d06f080 {R : Type} [CommRing R] {f : MvPolynomial (Σ k, ι k) R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (liftVar ι') f) (Sum.elim a 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointVerticalDivisor».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_isMultiHomog_rename_9ca82d06f080
