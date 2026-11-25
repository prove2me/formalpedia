-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_idealEquiv_apply_ed453f3bd221
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_idealEquiv_apply_ed453f3bd221
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:38:19.983801+00:00
-- url     : https://prove2.me/theorems/e412322e-6c71-45d8-8022-eab61cbb2835
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ideal Equiv apply ed453f3bd221: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ideal Equiv apply ed453f3bd221
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ideal Equiv apply ed453f3bd221 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Relabel ideal Equiv apply ed453f3bd221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberRelabel.lean#L44-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUniqueRelabel_idealEquiv_apply_240b37bfc4da

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
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_idealEquiv_apply_ed453f3bd221 (W : Ideal (MRing ι₁ R)) :
    idealEquiv (R := R) σ W = W.map (ren (R := R) σ : MRing ι₁ R →+* MRing ι₂ R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberRelabel».«idealEquiv_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_idealEquiv_apply_ed453f3bd221
