-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:39.097912+00:00
-- url     : https://prove2.me/theorems/69b02866-63b6-4498-bc90-a7f7aa5e5513
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point plane Pt injective df97cc17290a: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point plane Pt injective df97cc17
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point plane Pt injective df97cc17290a construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point plane Pt injective df97cc17290a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L119-L129

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a {D : ℕ} (y : Fin D → ℂ) :
    Function.Injective fun σ : K →+* ℂ =>
      segre (ι := projBlocks K (D + 1)) (projPlanePt σ (Fin.cons 1 y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«planePt_injective» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_planePt_injective_df97cc17290a
