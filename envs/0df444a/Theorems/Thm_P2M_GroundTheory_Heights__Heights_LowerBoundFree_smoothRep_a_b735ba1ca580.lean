-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_smoothRep_a_b735ba1ca580
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_smoothRep_a_b735ba1ca580
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:59.87318+00:00
-- url     : https://prove2.me/theorems/b192710b-4d25-5841-ab5e-e534cd98f5c1
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free smooth Rep a b735ba1ca580: P2 M Ground Theory Heights  Heights Lower Bound Free smooth Rep a b735ba1ca580
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free smooth Rep a b735ba1ca580 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free smooth Rep a b735ba1ca580 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Weights.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Weights.lean#L107-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
attribute [instance] CxModel.top CxModel.compact CxModel.t2
variable {P : Ideal (MRing ι)} {d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_smoothRep_a_b735ba1ca580 (P : Ideal (MRing ι)) (A : HermLine ι) : (smoothRep P A).a = A.a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«smoothRep_a» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_smoothRep_a_b735ba1ca580
