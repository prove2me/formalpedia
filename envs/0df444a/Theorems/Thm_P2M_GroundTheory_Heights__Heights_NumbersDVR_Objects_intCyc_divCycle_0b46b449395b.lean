-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:52.430434+00:00
-- url     : https://prove2.me/theorems/fb463662-9744-47d3-a8a5-a1171fefaea4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects int Cyc div Cycle 0b46b449395b: P2 M Ground Theory Heights  Heights Numbers DVR Objects int Cyc div Cycle 0b46b449395b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects int Cyc div Cycle 0b46b449395b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects int Cyc div Cycle 0b46b449395b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L64-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L64-L80

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
variable {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b [IsNoetherianRing R] (P : Ideal (MRing ι R)) (s : MRing ι R)
    (W : Ideal (MRing ι R)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
      divCycle P s W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«intCyc_divCycle» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_intCyc_divCycle_0b46b449395b
