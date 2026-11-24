-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:56.045775+00:00
-- url     : https://prove2.me/theorems/e954f425-5666-4d46-9ff9-7fecc24df40e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects is Multi Homog iff f0c1440da5d0: P2 M Ground Theory Heights  Heights Numbers DVR Objects is Multi Homog iff f0c1440da5d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects is Multi Homog iff f0c1440da5d0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects is Multi Homog iff f0c1440da5d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L28-L35

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0 (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0
