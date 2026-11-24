-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:15.425229+00:00
-- url     : https://prove2.me/theorems/d9e00a95-444e-4bce-970c-149782d0a92b
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point proj segre plane Pt 9c8c7cf829ad: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point proj segre plane Pt 9c8c7cf829ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point proj segre plane Pt 9c8c7cf829ad construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point proj segre plane Pt 9c8c7cf829ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L36-L42

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
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualProj b hb (segre (dualPlanePt b σ v)) = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«proj_segre_planePt» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_proj_segre_planePt_9c8c7cf829ad
