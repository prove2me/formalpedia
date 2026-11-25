-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_isRelevant_map_iff_73b1e612cfb4
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_isRelevant_map_iff_73b1e612cfb4
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:20.446749+00:00
-- url     : https://prove2.me/theorems/1fb292c4-5482-44ad-8737-155ae7c4a0dc
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity is Relevant map iff 73b1e612cfb4: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity is Relevant ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity is Relevant map iff 73b1e612cfb4 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity is Relevant map iff 73b1e612cfb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L156-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_isRelevant_map_iff_73b1e612cfb4 (W : Ideal (MRing (PBlk n))) :
    IsRelevant (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) ↔
      ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«isRelevant_map_iff» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_isRelevant_map_iff_73b1e612cfb4
