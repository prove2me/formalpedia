-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:08.965309+00:00
-- url     : https://prove2.me/theorems/fff4bf17-f488-4f44-a1af-358ebb4f9dc6
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm linear Form le d8b2dd900305: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm linear Form le d8b2dd900305
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm linear Form le d8b2dd900305 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm linear Form le d8b2dd900305 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L83-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305 {κ : Type*} [Fintype κ] (b : κ → L) (c : L)
    (hb : ∀ j, ‖b j‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    gaussNormOf (normAbv L) (∑ j, C (b j) * X j + C c : MvPolynomial κ L) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_linearForm_le» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_linearForm_le_d8b2dd900305
