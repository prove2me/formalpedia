-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:33.343554+00:00
-- url     : https://prove2.me/theorems/92464fba-14b8-4aec-ae15-a362ea78ee25
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img eq zero iff 1a7b10f3ef75: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img eq zero iff 1a7b10f3ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img eq zero iff 1a7b10f3ef75 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img eq zero iff 1a7b10f3ef75 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L40-L41

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75 {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingNoetherian».«img_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75
