-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:25.582462+00:00
-- url     : https://prove2.me/theorems/f5f64289-648d-4015-8c6c-4832c1ca5a27
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point emb Comp plane Pt 6ec18513afa5: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point emb Comp plane Pt 6ec18513af
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point emb Comp plane Pt 6ec18513afa5 construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point emb Comp plane Pt 6ec18513afa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L33-L42

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5 {i : ℕ} (τ σ : K →+* ℂ) (v : Fin i → ℂ) :
    embComp τ (fun q => projPlanePt σ v ⟨(), q⟩) = if σ = τ then v else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«embComp_planePt» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_embComp_planePt_6ec18513afa5
