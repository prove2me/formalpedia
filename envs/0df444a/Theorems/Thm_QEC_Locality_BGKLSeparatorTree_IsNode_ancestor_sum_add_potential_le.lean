-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_ancestor_sum_add_potential_le
-- name    : QEC.Locality.BGKLSeparatorTree.IsNode.ancestor_sum_add_potential_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:46.609822+00:00
-- url     : https://prove2.me/theorems/608e4227-4073-4ea5-83b0-79c9bfff2e3b
-- title:
--   Is Node: ancestor sum add potential le
-- statement:
--   The ancestor-separator geometric-series estimate, proved directly on the real
--   tree.  The residual term is retained, so the estimate does not appeal to an
--   assumed infinite-series bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L407-L434
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L407-L434

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Locality.BGKLSeparatorTree.IsNode.ancestor_sum_add_potential_le
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent) :
    (ancestorSeparatorCardSum ancestors : ℝ) +
        beta / (1 - bgklDecayRatio exponent) * Real.rpow node.card exponent ≤
      beta / (1 - bgklDecayRatio exponent) * Real.rpow root.card exponent := by sorry
