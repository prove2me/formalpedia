-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:54.966819+00:00
-- url     : https://prove2.me/theorems/1b0286de-474c-5366-b197-96a1fac436b3
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point h eq 9af9feb0e0d4: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point h eq 9af9feb0e0d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point h eq 9af9feb0e0d4 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point h eq 9af9feb0e0d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L44-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L44-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4 (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    (hz : z ∈ mcPts (dualIdeal b)) :
    (dualLine F b hb).h z = Real.sqrt (∑ j, ‖dualProj b hb (segre z) j‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«h_eq» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_h_eq_9af9feb0e0d4
