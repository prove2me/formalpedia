-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
-- name    : QEC.Locality.BGKLSeparatorTree.IsNode.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:41.740398+00:00
-- url     : https://prove2.me/theorems/17ecc967-8240-415d-a8cc-94bd012e2357
-- title:
--   Is Node: trans
-- statement:
--   Compose a root-to-subtree path with a path inside that subtree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L172-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L172-L189

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

theorem QEC.Locality.BGKLSeparatorTree.IsNode.trans
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat}
    {globalRoot localRoot node : Finset ι}
    {globalTree : BGKLSeparatorTree P d globalRoot}
    {localTree : BGKLSeparatorTree P d localRoot}
    {globalAncestors localAncestors : List (Finset ι)}
    (hGlobal : globalTree.IsNode localTree globalAncestors)
    (nodeTree : BGKLSeparatorTree P d node)
    (hLocal : localTree.IsNode nodeTree localAncestors) :
    globalTree.IsNode nodeTree (globalAncestors ++ localAncestors) := by sorry
