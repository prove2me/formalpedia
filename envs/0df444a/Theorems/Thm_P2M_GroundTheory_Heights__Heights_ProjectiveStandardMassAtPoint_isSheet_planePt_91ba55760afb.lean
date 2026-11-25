-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:35.569193+00:00
-- url     : https://prove2.me/theorems/4da23eac-1cea-430e-91bd-084839ec2954
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point is Sheet plane Pt 91ba55760afb: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point is Sheet plane Pt 91ba55760a
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point is Sheet plane Pt 91ba55760afb construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point is Sheet plane Pt 91ba55760afb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L131-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L131-L145

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb (hOf : ProjPtsOfPlane.Statement) {D : ℕ} (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (projSpaceIdeal K (D + 1)) projProj y
      (segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)))
      (fun y' => projPlanePt σ (Fin.cons 1 y')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«isSheet_planePt» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_isSheet_planePt_91ba55760afb
