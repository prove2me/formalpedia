-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_comap_le_1f0469125f95
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_comap_le_1f0469125f95
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:40.903683+00:00
-- url     : https://prove2.me/theorems/ab336819-f87c-4a27-962f-138c772ea63d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of comap le 1f0469125f95: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of comap le 1f0469125f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of comap le 1f0469125f95 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Of comap le 1f0469125f95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L43-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpHorizontalStrict.lean#L43-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpHorizontalStrict
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
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_comap_le_1f0469125f95 {P : Ideal (MRing ι R)} {u : J → MRing ι R} {H : Ideal (MRing (extIdx ι J) R)}
    (hH : H.IsPrime) (hPH : blowUpOf P u ≤ H) {j₀ : J}
    (hj₀ : u j₀ ∉ H.comap (liftForm (ι := ι) (J := J) (R := R))) :
    blowUpOf (H.comap (liftForm (ι := ι) (J := J) (R := R))) u ≤ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpOf_comap_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpOf_comap_le_1f0469125f95
