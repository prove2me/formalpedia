-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_absNorm_map_comap_C_24678f6aa93d
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_absNorm_map_comap_C_24678f6aa93d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:36.498896+00:00
-- url     : https://prove2.me/theorems/bd0966fa-8f9b-4da2-9838-89039df8f91d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity abs Norm map comap C 24678f6aa93d: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity abs Norm map
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity abs Norm map comap C 24678f6aa93d construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity abs Norm map comap C 24678f6aa93d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L231-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L231-L241

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_absNorm_map_comap_C_24678f6aa93d (W : Ideal (MRing (PBlk n))) :
    Ideal.absNorm ((W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«absNorm_map_comap_C» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_absNorm_map_comap_C_24678f6aa93d
