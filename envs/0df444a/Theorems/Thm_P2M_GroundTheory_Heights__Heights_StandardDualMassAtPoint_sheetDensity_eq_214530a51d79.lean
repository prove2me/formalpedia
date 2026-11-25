-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:07.48182+00:00
-- url     : https://prove2.me/theorems/d8ac91a1-70d6-5815-a8ac-0f780e064966
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Mass At Point sheet Density eq 214530a51d79: P2 M Ground Theory Heights  Heights Standard Dual Mass At Point sheet Density eq 214530a51d79
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Mass At Point sheet Density eq 214530a51d79 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Mass At Point sheet Density eq 214530a51d79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdMassAt.lean#L67-L81

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79 (hOn : DualPtsOnPlane.Statement) {D : ℕ} {F : HermLattice K (D + 1)}
    (hF : ∀ σ, F.metric σ = 1) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {y : Fin D → ℂ}
    {w : ((k : Unit) → dualBlocks T k) → ℂ} (h : ∃ γ, IsSheet (dualIdeal b) (dualProj b hb) y w γ) :
    sheetDensity (dualIdeal b) (dualProj b hb) (fun _ z => Real.log ((dualLine F b hb).h z))
      (fun _ => 1) y w = maDensity (fun _ : Fin D => gbPot) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualMassAtPoint».«sheetDensity_eq» := P2M_GroundTheory_Heights__Heights_StandardDualMassAtPoint_sheetDensity_eq_214530a51d79
