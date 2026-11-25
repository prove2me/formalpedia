-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:53.02285+00:00
-- url     : https://prove2.me/theorems/9ee97255-c5ac-465e-be99-86b783d6be9b
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point repr sum de623f64b805: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point repr sum de623f64b805
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point repr sum de623f64b805 construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point repr sum de623f64b805 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PProjStdMassAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectiveStandardMassAtPoint
variable {K : Type} [Field K] [NumberField K]
open Classical

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805 (τ σ : K →+* ℂ) :
    ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«repr_sum» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_repr_sum_de623f64b805
