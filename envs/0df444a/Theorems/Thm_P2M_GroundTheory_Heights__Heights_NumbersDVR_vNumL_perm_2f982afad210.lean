-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_perm_2f982afad210
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_perm_2f982afad210
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:40.997223+00:00
-- url     : https://prove2.me/theorems/f16a7e4a-f746-4e59-b468-10240e74fbc1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num L perm 2f982afad210: P2 M Ground Theory Heights  Heights Numbers DVR v Num L perm 2f982afad210
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num L perm 2f982afad210 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num L perm 2f982afad210 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L226-L228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_perm_2f982afad210 (W : Ideal (MRing ι O)) {l₁ l₂ : List (K → ℤ)} (hl : l₁.Perm l₂) :
    vNumL W l₁ = vNumL W l₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNumL_perm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_perm_2f982afad210
