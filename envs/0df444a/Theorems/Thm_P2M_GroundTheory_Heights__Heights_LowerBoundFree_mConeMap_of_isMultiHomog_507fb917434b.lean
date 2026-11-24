-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:50.054545+00:00
-- url     : https://prove2.me/theorems/056dfefd-2a18-4fc4-bb91-a77117f27730
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free m Cone Map of is Multi Homog 507fb917434b: P2 M Ground Theory Heights  Heights Lower Bound Free m Cone Map of is Multi Homog 507fb917434b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free m Cone Map of is Multi Homog 507fb917434b construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free m Cone Map of is Multi Homog 507fb917434b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L47-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/MemMCoordIdealOfAevalEqZero.lean#L47-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«mConeMap_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_mConeMap_of_isMultiHomog_507fb917434b
