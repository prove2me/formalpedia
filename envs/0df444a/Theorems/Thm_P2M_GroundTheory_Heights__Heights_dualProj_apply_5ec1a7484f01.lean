-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01
-- name    : P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:20.872102+00:00
-- url     : https://prove2.me/theorems/f877d7dc-a691-4ad3-b534-aab1c44051a2
-- title:
--   P2 M Ground Theory Heights  Heights dual Proj apply 5ec1a7484f01: P2 M Ground Theory Heights  Heights dual Proj apply 5ec1a7484f01
-- statement:
--   The P2 M Ground Theory Heights  Heights dual Proj apply 5ec1a7484f01 construction uses the P2 M Ground Theory Heights  Heights dual Proj apply 5ec1a7484f01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DualProjApply.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/DualProjApply.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualProjApply
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (s : ((k : Unit) → dualBlocks T k) → ℂ) (j : Fin i) :
    dualProj b hb s j = ∑ σ : K →+* ℂ, dualRecover b hb (fun t => s fun _ => t) (σ, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«dualProj_apply» := P2M_GroundTheory_Heights__Heights_dualProj_apply_5ec1a7484f01
