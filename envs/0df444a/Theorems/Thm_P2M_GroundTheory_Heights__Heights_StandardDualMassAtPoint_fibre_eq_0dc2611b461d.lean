-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:25.599555+00:00
-- url     : https://prove2.me/theorems/69f6eb35-73ec-41b2-9fc0-e0bbcf1abfdd
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point fibre eq 0dc2611b461d: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point fibre eq 0dc2611b461d
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point fibre eq 0dc2611b461d construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point fibre eq 0dc2611b461d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L83-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L83-L110

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement) {D : ℕ}
    {F : HermLattice K (D + 1)} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (y : Fin D → ℂ) :
    fibre (dualIdeal b) (dualProj b hb) y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«fibre_eq» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_fibre_eq_0dc2611b461d
