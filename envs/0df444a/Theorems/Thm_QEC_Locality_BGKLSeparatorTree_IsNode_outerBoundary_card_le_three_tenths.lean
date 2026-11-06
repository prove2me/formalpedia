-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_outerBoundary_card_le_three_tenths
-- name    : QEC.Locality.BGKLSeparatorTree.IsNode.outerBoundary_card_le_three_tenths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:43.971881+00:00
-- url     : https://prove2.me/theorems/4d800db2-9317-4c33-bcae-6ae092b95cb2
-- title:
--   Is Node: outer Boundary card le three tenths
-- statement:
--   Every tree-node boundary obeys the source's `3d/10` estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L491-L521
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L491-L521

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

theorem QEC.Locality.BGKLSeparatorTree.IsNode.outerBoundary_card_le_three_tenths
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {d : Nat} {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors)
    {beta exponent : ℝ} (hd : 0 < d)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hSmall : (root.card : ℝ) ≤ Real.rpow
      (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hRootBoundary : 4 * (fixedGeneratorOuterBoundaryFinset P root).card ≤ d) :
    ((fixedGeneratorOuterBoundaryFinset P node).card : ℝ) ≤ 3 * (d : ℝ) / 10 := by sorry
