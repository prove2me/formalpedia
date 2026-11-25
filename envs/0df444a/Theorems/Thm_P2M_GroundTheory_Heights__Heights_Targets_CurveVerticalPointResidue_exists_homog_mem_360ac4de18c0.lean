-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_mem_360ac4de18c0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_mem_360ac4de18c0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:58.582978+00:00
-- url     : https://prove2.me/theorems/ec8cc0fc-d043-5461-9a2e-a27d42b6b9a2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog mem 360ac4de18c0: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog mem 360ac4
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog mem 360ac4de18c0 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue exists homog mem 360ac4de18c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L72-L98

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_mem_360ac4de18c0 {S : Type*} [CommRing S] (χ : MRing ι →+* S) (c : ∀ k, ι k)
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {f : MRing ι} (hf : f ∈ W) :
    ∃ (n : K → ℕ) (G : MRing ι), G ∈ W ∧ IsMultiHomog G n ∧ χ G = χ f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«exists_homog_mem» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_exists_homog_mem_360ac4de18c0
