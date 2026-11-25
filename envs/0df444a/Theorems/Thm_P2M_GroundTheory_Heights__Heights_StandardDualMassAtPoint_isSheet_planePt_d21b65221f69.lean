-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_isSheet_planePt_d21b65221f69
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_isSheet_planePt_d21b65221f69
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:51.048923+00:00
-- url     : https://prove2.me/theorems/770eff1c-9af2-5b10-b398-03adda4febaf
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point is Sheet plane Pt d21b65221f69: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point is Sheet plane Pt d21b65221f69
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point is Sheet plane Pt d21b65221f69 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point is Sheet plane Pt d21b65221f69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L124-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L124-L139

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_isSheet_planePt_d21b65221f69 (hOf : DualPtsOfPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (y : Fin D → ℂ) :
    IsSheet (dualIdeal b) (dualProj b hb) y (segre (ι := dualBlocks T) (dualPlanePt b σ (Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (Fin.cons 1 y')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«isSheet_planePt» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_isSheet_planePt_d21b65221f69
