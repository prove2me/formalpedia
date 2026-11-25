-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:44.085588+00:00
-- url     : https://prove2.me/theorems/810d578c-469b-4117-a249-d0ab5ad9546f
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point fibre eq 077cda411379: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point fibre eq 077cda411379
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point fibre eq 077cda411379 construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point fibre eq 077cda411379 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L89-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L89-L117

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379 (hOn : ProjPtsOnPlane.Statement) (hOf : ProjPtsOfPlane.Statement) {D : ℕ}
    (y : Fin D → ℂ) :
    fibre (projSpaceIdeal K (D + 1)) projProj y =
      Set.range fun σ : K →+* ℂ => segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«fibre_eq» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_fibre_eq_077cda411379
