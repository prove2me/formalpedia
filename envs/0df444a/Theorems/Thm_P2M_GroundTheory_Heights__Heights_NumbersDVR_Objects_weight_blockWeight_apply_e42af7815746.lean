-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:40.947801+00:00
-- url     : https://prove2.me/theorems/6a799fa3-8ba8-42e7-9c60-2b1be9987855
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Objects weight block Weight apply e42af7815746: P2 M Ground Theory Heights  Heights Numbers DVR Objects weight block Weight apply e42af7815746
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Objects weight block Weight apply e42af7815746 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Objects weight block Weight apply e42af7815746 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisorAlt.lean#L20-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
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
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746 (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«Objects».«weight_blockWeight_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_weight_blockWeight_apply_e42af7815746
