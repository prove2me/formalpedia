-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:20.086738+00:00
-- url     : https://prove2.me/theorems/f8748389-d431-4af7-b00c-1602112f5965
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map equiv 39fad21a977d: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map equiv 39fad21a977d construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity local Mult map equiv 39fad21a977d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L39-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L39-L85

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d {A B : Type*} [CommRing A] [CommRing B] (Ψ : A ≃+* B) (K W : Ideal A) :
    localMult (K.map (Ψ : A →+* B)) (W.map (Ψ : A →+* B)) = localMult K W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«localMult_map_equiv» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_localMult_map_equiv_39fad21a977d
