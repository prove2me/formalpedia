-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_map_aeval_int_7997e94014c7
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_map_aeval_int_7997e94014c7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:20.383116+00:00
-- url     : https://prove2.me/theorems/a03bda46-e336-5a77-a8da-ca76de1867bc
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity map aeval int 7997e94014c7: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity map aeval int 79
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity map aeval int 7997e94014c7 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity map aeval int 7997e94014c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointMultChart.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointMultChart.lean#L33-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointMultChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointMultiplicity
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_map_aeval_int_7997e94014c7 {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (r : (Σ k, ι k) → S)
    (f : MRing ι) : φ (aeval r f) = aeval (fun p => φ (r p)) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointMultiplicity».«map_aeval_int» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_map_aeval_int_7997e94014c7
