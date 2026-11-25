-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:28.752359+00:00
-- url     : https://prove2.me/theorems/5117700d-47f0-4dd9-8f1e-3f27008d36f7
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval eq eval  e50f1199a6e0: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval eq eval  e50f1199a6e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval eq eval  e50f1199a6e0 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval eq eval  e50f1199a6e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointNagata
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
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0 {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S) (f : MRing ι) :
    aeval v f = eval₂ (Int.castRingHom S) v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointNagata».«aeval_eq_eval₂» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0
