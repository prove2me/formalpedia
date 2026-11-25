-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_aestronglyMeasurable_47b600fa3ffa
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosDens_aestronglyMeasurable_47b600fa3ffa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:57.853494+00:00
-- url     : https://prove2.me/theorems/e0fc4806-b446-47a0-8b47-1d153222ae65
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Dens aestrongly Measurable 47b600fa3ffa: P2 M Ground Theory Heights  Heights Pts Pos Dens aestrongly Measurable 47b600fa3ffa
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Dens aestrongly Measurable 47b600fa3ffa construction uses the P2 M Ground Theory Heights  Heights Pts Pos Dens aestrongly Measurable 47b600fa3ffa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L102-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L102-L226

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsPosDens_aestronglyMeasurable_47b600fa3ffa {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι}
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) :
    AEStronglyMeasurable (ptsPosDens P Ψ (pot L) g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosDens».«aestronglyMeasurable» := P2M_GroundTheory_Heights__Heights_PtsPosDens_aestronglyMeasurable_47b600fa3ffa
