-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
-- name    : P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:04.051338+00:00
-- url     : https://prove2.me/theorems/8e665db3-1948-4618-b0a9-25ede725f8d9
-- title:
--   P2 M Ground Theory Heights  Heights Projective Standard Mass At Point segre const 65478bf974b7: P2 M Ground Theory Heights  Heights Projective Standard Mass At Point segre const 65478bf974b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Projective Standard Mass At Point segre const 65478bf974b7 construction uses the P2 M Ground Theory Heights  Heights Projective Standard Mass At Point segre const 65478bf974b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PProjStdMassAt.lean#L17-L19

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

theorem P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7 {i : ℕ} (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (q : ProjIdx K i) :
    segre (ι := projBlocks K i) z (fun _ => q) = z ⟨(), q⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectiveStandardMassAtPoint».«segre_const» := P2M_GroundTheory_Heights__Heights_ProjectiveStandardMassAtPoint_segre_const_65478bf974b7
