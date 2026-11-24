-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:39.5289+00:00
-- url     : https://prove2.me/theorems/ad59bc4b-5f34-4798-8505-7b1d3c6e4754
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point recover plane Pt b75c0350c21e: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point recover plane Pt b75c0350c21e
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point recover plane Pt b75c0350c21e construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point recover plane Pt b75c0350c21e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L25-L32

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e {i : ℕ} {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin i → ℂ) :
    dualRecover b hb (fun t => dualPlanePt b σ v ⟨(), t⟩) =
      fun p => if p.1 = σ then v p.2 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«recover_planePt» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_recover_planePt_b75c0350c21e
