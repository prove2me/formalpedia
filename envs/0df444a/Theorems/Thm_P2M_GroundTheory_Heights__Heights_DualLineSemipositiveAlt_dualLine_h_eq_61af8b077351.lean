-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351
-- name    : P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:52.585606+00:00
-- url     : https://prove2.me/theorems/b17cc08e-5c54-5498-baef-beb2755043ca
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt dual Line h eq 61af8b077351: P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt dual Line h eq 61af8b077351
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt dual Line h eq 61af8b077351 construction uses the P2 M Ground Theory Heights  Heights Dual Line Semipositive Alt dual Line h eq 61af8b077351 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean#L51-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineSemipositiveAlt
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351 {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ) :
    (dualLine F b hb).h z = (fsMetric ((K →+* ℂ) × Fin i)).ρ (coordMap b hb z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineSemipositiveAlt».«dualLine_h_eq» := P2M_GroundTheory_Heights__Heights_DualLineSemipositiveAlt_dualLine_h_eq_61af8b077351
