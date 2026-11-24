-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:43.64781+00:00
-- url     : https://prove2.me/theorems/c9d652c0-d424-4748-99b9-b36e58135100
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog b690ef546a3c: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog b690ef546a3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog b690ef546a3c construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog b690ef546a3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L51-L70

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c {S : Type*} [CommRing S] (χ : MRing ι →+* S) (c : ∀ k, ι k)
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (f : MRing ι) :
    ∃ (n : K → ℕ) (G : MRing ι), IsMultiHomog G n ∧ χ G = χ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«exists_homog» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_b690ef546a3c
