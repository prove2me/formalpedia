-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:30.867713+00:00
-- url     : https://prove2.me/theorems/62900e35-9751-4636-9608-b9c7d44479af
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects div O eq rat Div c8baeb4d1a16: P2 M Ground Theory Heights  Heights Numbers DVR Objects div O eq rat Div c8baeb4d1a16
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects div O eq rat Div c8baeb4d1a16 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects div O eq rat Div c8baeb4d1a16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L88-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
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
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16 (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«divO_eq_ratDiv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_divO_eq_ratDiv_c8baeb4d1a16
