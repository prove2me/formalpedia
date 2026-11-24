-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1
-- name    : P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:33.594829+00:00
-- url     : https://prove2.me/theorems/22c67fa4-19c6-4266-9548-d8fc6e8f04ec
-- title:
--   P2 M Ground Theory Heights  Heights height eq block Sum d5c0c59058d1: P2 M Ground Theory Heights  Heights height eq block Sum d5c0c59058d1
-- statement:
--   The P2 M Ground Theory Heights  Heights height eq block Sum d5c0c59058d1 construction uses the P2 M Ground Theory Heights  Heights height eq block Sum d5c0c59058d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L201-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L201-L232

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1 (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ))
    (hx : BlockNonzero x) :
    height A x = ((Module.finrank ℚ (coordField x) : ℝ))⁻¹ *
      (∑ k, (A.deg k : ℝ) * blockSum (coordVec x) k +
        ∑ σ : coordField x →+* ℂ, metricDefect A (fun k i ↦ σ (coordVec x k i))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_eq_blockSum» := P2M_GroundTheory_Heights__Heights_height_eq_blockSum_d5c0c59058d1
