-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_outerBoundary_subset
-- name    : QEC.Locality.BGKLSeparatorTree.IsNode.outerBoundary_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:13.572022+00:00
-- url     : https://prove2.me/theorems/6e5fe703-9148-4e71-91d6-3ed19b20f0fd
-- title:
--   Is Node: outer Boundary subset
-- statement:
--   Every node boundary is covered by the root boundary and ancestor separators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L269-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L269-L299

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

theorem QEC.Locality.BGKLSeparatorTree.IsNode.outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat}
    {root node : Finset ι} {tree : BGKLSeparatorTree P d root}
    {nodeTree : BGKLSeparatorTree P d node}
    {ancestors : List (Finset ι)} (hnode : tree.IsNode nodeTree ancestors) :
    fixedGeneratorOuterBoundaryFinset P node ⊆
      fixedGeneratorOuterBoundaryFinset P root ∪ ancestorSeparatorUnion ancestors := by sorry
