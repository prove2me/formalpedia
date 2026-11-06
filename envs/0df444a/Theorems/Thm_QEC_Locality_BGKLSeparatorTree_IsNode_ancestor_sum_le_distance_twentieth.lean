-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_ancestor_sum_le_distance_twentieth
-- name    : QEC.Locality.BGKLSeparatorTree.IsNode.ancestor_sum_le_distance_twentieth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:58.628354+00:00
-- url     : https://prove2.me/theorems/b876ac1a-7c11-4cf8-bada-e0c59fee1825
-- title:
--   Is Node: ancestor sum le distance twentieth
-- statement:
--   The source-size hypothesis converts exactly to the `d/20` path budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L443-L476
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L443-L476

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

theorem QEC.Locality.BGKLSeparatorTree.IsNode.ancestor_sum_le_distance_twentieth
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹) :
    (ancestorSeparatorCardSum ancestors : ℝ) ≤ (d : ℝ) / 20 := by sorry
