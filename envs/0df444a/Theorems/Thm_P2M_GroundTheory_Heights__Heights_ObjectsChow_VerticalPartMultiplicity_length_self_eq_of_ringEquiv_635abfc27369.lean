-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_self_eq_of_ringEquiv_635abfc27369
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_self_eq_of_ringEquiv_635abfc27369
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:58.195231+00:00
-- url     : https://prove2.me/theorems/d6593439-933e-4df1-8aa3-7b2d43bdf8ee
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity length self eq of ring Equiv 635abfc27369: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity lengt
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity length self eq of ring Equiv 635abfc27369 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity length self eq of ring Equiv 635abfc27369 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L31-L37

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_self_eq_of_ringEquiv_635abfc27369 {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«length_self_eq_of_ringEquiv» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_length_self_eq_of_ringEquiv_635abfc27369
