-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:10.299293+00:00
-- url     : https://prove2.me/theorems/1579f68c-d788-4f50-a439-29b50600a165
-- title:
--   P2 M Ground Theory Heights  Heights Model exists multiple int cbe6eae920c5: P2 M Ground Theory Heights  Heights Model exists multiple int cbe6eae920c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists multiple int cbe6eae920c5 construction uses the P2 M Ground Theory Heights  Heights Model exists multiple int cbe6eae920c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L701-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L701-L714

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5 (M : Submonoid ℤ) (hM : (0 : ℤ) ∉ M) (o : Type) [CommRing o]
    [Algebra ℤ o] [IsLocalization M o] (φ : o →+* ℚ) (a : o) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * φ a = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_multiple_int» := P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5
