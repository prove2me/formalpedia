-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_reduceMod_map_777fc4698e51
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_reduceMod_map_777fc4698e51
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:06.335533+00:00
-- url     : https://prove2.me/theorems/cbff2ad4-9752-4f01-9529-ccd401c4022f
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity reduce Mod map 777fc4698e51: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity reduce Mod map 777f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity reduce Mod map 777fc4698e51 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity reduce Mod map 777fc4698e51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L218-L229

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_reduceMod_map_777fc4698e51 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (W : Ideal (MRing (PBlk n))) :
    reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom v.asIdeal.ResidueField)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«reduceMod_map» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_reduceMod_map_777fc4698e51
