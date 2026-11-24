-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
-- name    : P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:25.956019+00:00
-- url     : https://prove2.me/theorems/31e2fdeb-f383-4cb5-8224-b95a11e53fe0
-- title:
--   P2 M Ground Theory Heights  Heights Centred Ring Normal is Integral of comp 3ac7131e96c4: P2 M Ground Theory Heights  Heights Centred Ring Normal is Integral of comp 3ac7131e96c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Centred Ring Normal is Integral of comp 3ac7131e96c4 construction uses the P2 M Ground Theory Heights  Heights Centred Ring Normal is Integral of comp 3ac7131e96c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PCentredRingNormal.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightCentredRingNormal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PCentredRingNormal
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
open NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights.CentredRingNormal
variable {L : Type} [Field L] [NumberField L]
omit [NumberField L]

theorem P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4 {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R L] [Algebra R' L]
    (f : R →+* R') (hf : (algebraMap R' L).comp f = algebraMap R L) {x : L}
    (hx : IsIntegral R x) : IsIntegral R' x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CentredRingNormal».«isIntegral_of_comp» := P2M_GroundTheory_Heights__Heights_CentredRingNormal_isIntegral_of_comp_3ac7131e96c4
