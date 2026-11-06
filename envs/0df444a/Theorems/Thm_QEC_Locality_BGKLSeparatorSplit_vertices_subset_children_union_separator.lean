-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_vertices_subset_children_union_separator
-- name    : QEC.Locality.BGKLSeparatorSplit.vertices_subset_children_union_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:45.09781+00:00
-- url     : https://prove2.me/theorems/8dccd181-f2b8-4219-9a77-893502ed0d17
-- title:
--   BGKLSeparator Split: vertices subset children union separator
-- statement:
--   A branch's retained children form the exact parent-minus-separator region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L538-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L538-L547

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

theorem QEC.Locality.BGKLSeparatorSplit.vertices_subset_children_union_separator
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    vertices ⊆ (split.left ∪ split.right) ∪ split.separator := by sorry
