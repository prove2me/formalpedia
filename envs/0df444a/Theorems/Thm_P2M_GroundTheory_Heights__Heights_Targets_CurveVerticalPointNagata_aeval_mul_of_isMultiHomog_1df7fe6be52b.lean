-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_mul_of_isMultiHomog_1df7fe6be52b
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_mul_of_isMultiHomog_1df7fe6be52b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:26.292516+00:00
-- url     : https://prove2.me/theorems/d84797e5-ea68-43ca-86f6-6ba98c7cdfd0
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval mul of is Multi Homog 1df7fe6be52b: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval mul of i
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval mul of is Multi Homog 1df7fe6be52b construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval mul of is Multi Homog 1df7fe6be52b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L31-L49

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_mul_of_isMultiHomog_1df7fe6be52b {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {g : MRing ι}
    {e : K → ℕ} (hg : IsMultiHomog g e) :
    aeval (fun p => r p * t p.1) g = aeval r g * ∏ k, t k ^ e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointNagata».«aeval_mul_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_mul_of_isMultiHomog_1df7fe6be52b
