-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:39.522906+00:00
-- url     : https://prove2.me/theorems/781d8e65-507a-4306-a718-f18fe50e3c85
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point sheet Density eq 9d629b041c12: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point sheet Density eq 9d629b041c12
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point sheet Density eq 9d629b041c12 construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point sheet Density eq 9d629b041c12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L73-L87

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12 (hOn : ProjPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) {y : Fin D → ℂ}
    {w : ((k : Unit) → projBlocks K (D + 1) k) → ℂ}
    (h : ∃ γ, IsSheet (projSpaceIdeal K (D + 1)) projProj y w γ) :
    sheetDensity (projSpaceIdeal K (D + 1)) projProj (fun _ z => Real.log ((latticeLine F).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«sheetDensity_eq» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_sheetDensity_eq_9d629b041c12
