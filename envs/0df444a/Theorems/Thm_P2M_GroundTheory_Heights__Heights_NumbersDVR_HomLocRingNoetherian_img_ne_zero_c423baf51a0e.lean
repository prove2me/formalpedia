-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:42.726316+00:00
-- url     : https://prove2.me/theorems/2caf9ada-4ab5-489d-bfbc-5245ba892bea
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img ne zero c423baf51a0e: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img ne zero c423baf51a0e
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img ne zero c423baf51a0e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Noetherian img ne zero c423baf51a0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingNoetherian.lean#L53-L54

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingNoetherian».«img_ne_zero» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e
