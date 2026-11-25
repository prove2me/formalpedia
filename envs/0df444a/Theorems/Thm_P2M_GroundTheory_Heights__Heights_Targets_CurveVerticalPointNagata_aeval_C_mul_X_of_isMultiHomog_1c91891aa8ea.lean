-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_C_mul_X_of_isMultiHomog_1c91891aa8ea
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_C_mul_X_of_isMultiHomog_1c91891aa8ea
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:33.707471+00:00
-- url     : https://prove2.me/theorems/b89d3252-a5fe-547b-8ad4-30d57ebaa3e9
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval C mul X of is Multi Homog 1c91891aa8ea: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval C mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval C mul X of is Multi Homog 1c91891aa8ea construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata aeval C mul X of is Multi Homog 1c91891aa8ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L51-L60

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_C_mul_X_of_isMultiHomog_1c91891aa8ea {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (MvPolynomial K S)] (r : (Σ k, ι k) → S) {g : MRing ι}
    {e : K → ℕ} (hg : IsMultiHomog g e) :
    (aeval (fun p => MvPolynomial.C (r p) * MvPolynomial.X p.1) g : MvPolynomial K S) =
      MvPolynomial.C (aeval r g) * ∏ k, (MvPolynomial.X k : MvPolynomial K S) ^ e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointNagata».«aeval_C_mul_X_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_C_mul_X_of_isMultiHomog_1c91891aa8ea
