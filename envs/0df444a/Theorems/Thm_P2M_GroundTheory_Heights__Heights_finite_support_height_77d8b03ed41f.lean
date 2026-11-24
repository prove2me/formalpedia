-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f
-- name    : P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:43.204543+00:00
-- url     : https://prove2.me/theorems/f4a1fc56-dc76-4ff7-aa2f-bc53e73d30ee
-- title:
--   P2 M Ground Theory Heights  Heights finite support height 77d8b03ed41f: P2 M Ground Theory Heights  Heights finite support height 77d8b03ed41f
-- statement:
--   The P2 M Ground Theory Heights  Heights finite support height 77d8b03ed41f construction uses the P2 M Ground Theory Heights  Heights finite support height 77d8b03ed41f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FiniteSupportHeight.lean#L36-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
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

theorem P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (A : HermLine n)
    (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x) :
    (Function.support fun v : FinitePlace (coordField x) ↦
      ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finite_support_height» := P2M_GroundTheory_Heights__Heights_finite_support_height_77d8b03ed41f
