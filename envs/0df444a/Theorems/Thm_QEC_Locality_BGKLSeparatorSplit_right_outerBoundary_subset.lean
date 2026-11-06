-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_right_outerBoundary_subset
-- name    : QEC.Locality.BGKLSeparatorSplit.right_outerBoundary_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:02.605196+00:00
-- url     : https://prove2.me/theorems/8d20ddd3-1a7d-4679-a5c2-56e00277d42a
-- title:
--   BGKLSeparator Split: right outer Boundary subset
-- statement:
--   A right child's outer boundary lies in the parent's boundary or separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L220-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L220-L246

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

theorem QEC.Locality.BGKLSeparatorSplit.right_outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    fixedGeneratorOuterBoundaryFinset P split.right ⊆
      fixedGeneratorOuterBoundaryFinset P vertices ∪ split.separator := by sorry
