-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:56.404854+00:00
-- url     : https://prove2.me/theorems/5f6bc9a6-6357-4870-ba71-dffee0e35dcd
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound le nat Cast of lt nat Cast succ e06a86729995: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound le nat Cast of lt nat Cast s
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound le nat Cast of lt nat Cast succ e06a86729995 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound le nat Cast of lt nat Cast succ e06a86729995 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L64-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995 {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«le_natCast_of_lt_natCast_succ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_le_natCast_of_lt_natCast_succ_e06a86729995
