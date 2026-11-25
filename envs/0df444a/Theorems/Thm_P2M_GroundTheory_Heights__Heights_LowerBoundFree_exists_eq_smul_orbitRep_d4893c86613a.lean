-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:08.000138+00:00
-- url     : https://prove2.me/theorems/a8fbe967-f1f8-4932-a261-c519d161083d
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free exists eq smul orbit Rep d4893c86613a: P2 M Ground Theory Heights  Heights Lower Bound Free exists eq smul orbit Rep d4893c86613a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free exists eq smul orbit Rep d4893c86613a construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free exists eq smul orbit Rep d4893c86613a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L100-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a (z : (Σ k, ι k) → ℂ) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (orbitRep z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«exists_eq_smul_orbitRep» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_eq_smul_orbitRep_d4893c86613a
