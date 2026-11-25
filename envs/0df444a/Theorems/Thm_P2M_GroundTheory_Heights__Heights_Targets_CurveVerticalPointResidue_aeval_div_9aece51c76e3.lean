-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_aeval_div_9aece51c76e3
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_aeval_div_9aece51c76e3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:34.503672+00:00
-- url     : https://prove2.me/theorems/6d61f28d-8502-4ec7-9347-82318c31c8df
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue aeval div 9aece51c76e3: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue aeval div 9aece51c76e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue aeval div 9aece51c76e3 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue aeval div 9aece51c76e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L100-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L100-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_aeval_div_9aece51c76e3 {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (G : MRing ι) (n : K → ℕ) (hG : IsMultiHomog G n) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = aeval y G * (∏ k, y ⟨k, c k⟩ ^ n k)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«aeval_div» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_aeval_div_9aece51c76e3
