-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:59.553841+00:00
-- url     : https://prove2.me/theorems/d963e176-192b-5d2a-94e1-559ecfa391e2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img component congr 4af0000f3a87: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img component congr 4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img component congr 4af0000f3a87 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img component congr 4af0000f3a87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L43-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
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
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingNoetherian
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι R)) [P.IsPrime]
variable {P}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87 (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingNoetherian».«img_component_congr» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87
