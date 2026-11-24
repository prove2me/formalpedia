-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134
-- name    : P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:14.380832+00:00
-- url     : https://prove2.me/theorems/cfdb2561-c46a-4acb-8289-dae257c7f39e
-- title:
--   P2 M Ground Theory Heights  Heights Closed Point Unit Section exists valuation Subring 4a93cd2d9134: P2 M Ground Theory Heights  Heights Closed Point Unit Section exists valuation Subring 4a93cd2d9134
-- statement:
--   The P2 M Ground Theory Heights  Heights Closed Point Unit Section exists valuation Subring 4a93cd2d9134 construction uses the P2 M Ground Theory Heights  Heights Closed Point Unit Section exists valuation Subring 4a93cd2d9134 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsClosedPointUnitSection.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsClosedPointUnitSection.lean#L11-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
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
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134 {K : Type*} [Field K] (A : Subring K)
    (P : Ideal A) [P.IsPrime] :
    ∃ W : ValuationSubring K, (∀ a : A, (a : K) ∈ W) ∧ (∀ a : A, a ∉ P → W.valuation (a : K) = 1) ∧
      ∀ a : A, a ∈ P → W.valuation (a : K) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ClosedPointUnitSection».«exists_valuationSubring» := P2M_GroundTheory_Heights__Heights_ClosedPointUnitSection_exists_valuationSubring_4a93cd2d9134
