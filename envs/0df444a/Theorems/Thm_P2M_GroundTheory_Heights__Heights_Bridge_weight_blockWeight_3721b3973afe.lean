-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:27.731724+00:00
-- url     : https://prove2.me/theorems/2a4c038a-8fd1-44c7-9d2c-ff84bc2d5d7d
-- title:
--   P2 M Ground Theory Heights  Heights Bridge weight block Weight 3721b3973afe: P2 M Ground Theory Heights  Heights Bridge weight block Weight 3721b3973afe
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge weight block Weight 3721b3973afe construction uses the P2 M Ground Theory Heights  Heights Bridge weight block Weight 3721b3973afe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L21-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«weight_blockWeight» := P2M_GroundTheory_Heights__Heights_Bridge_weight_blockWeight_3721b3973afe
