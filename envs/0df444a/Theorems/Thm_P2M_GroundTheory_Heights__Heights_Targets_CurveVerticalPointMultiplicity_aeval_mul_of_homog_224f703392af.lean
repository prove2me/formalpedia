-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_aeval_mul_of_homog_224f703392af
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_aeval_mul_of_homog_224f703392af
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:20.244027+00:00
-- url     : https://prove2.me/theorems/7f4a76dc-de78-4600-a6bf-41d2e185caef
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity aeval mul of homog 224f703392af: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity aeval mul o
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity aeval mul of homog 224f703392af construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Multiplicity aeval mul of homog 224f703392af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointMultChart.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointMultChart.lean#L17-L31

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_aeval_mul_of_homog_224f703392af [Fintype K] [∀ k, Fintype (ι k)] {S : Type*} [CommRing S] [Algebra ℤ S] (r : (Σ k, ι k) → S) (t : K → S) {f : MRing ι}
    {d : K → ℕ} (hf : IsMultiHomog f d) :
    aeval (fun p => r p * t p.1) f = aeval r f * ∏ k, t k ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointMultiplicity».«aeval_mul_of_homog» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointMultiplicity_aeval_mul_of_homog_224f703392af
