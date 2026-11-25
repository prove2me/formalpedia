-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_eq_multAt_b5bbe6a474e9
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_eq_multAt_b5bbe6a474e9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:20.701109+00:00
-- url     : https://prove2.me/theorems/943cdfa7-e78e-421b-8ea2-1e8a410f324d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map eq mult At b5bbe6a474e9: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map eq mult At b5bbe6a474e9 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map eq mult At b5bbe6a474e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L163-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L163-L173

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_eq_multAt_b5bbe6a474e9 (K W : Ideal (MRing (PBlk n))) :
    localMult (K.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
        (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt K W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«localMult_map_eq_multAt» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_eq_multAt_b5bbe6a474e9
