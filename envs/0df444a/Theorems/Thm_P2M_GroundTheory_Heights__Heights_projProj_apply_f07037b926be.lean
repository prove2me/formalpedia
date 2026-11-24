-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be
-- name    : P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:50.583836+00:00
-- url     : https://prove2.me/theorems/5810238a-a5f4-4053-ab82-60c5af969c80
-- title:
--   P2 M Ground Theory Heights  Heights proj Proj apply f07037b926be: P2 M Ground Theory Heights  Heights proj Proj apply f07037b926be
-- statement:
--   The P2 M Ground Theory Heights  Heights proj Proj apply f07037b926be construction uses the P2 M Ground Theory Heights  Heights proj Proj apply f07037b926be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ProjProjApply.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ProjProjApply.lean#L24-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ProjProjApply
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
variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be (s : ((k : Unit) → projBlocks K i k) → ℂ) :
    projProj s = ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«projProj_apply» := P2M_GroundTheory_Heights__Heights_projProj_apply_f07037b926be
