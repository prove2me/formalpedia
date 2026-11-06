-- Prove2me | Theorems.Thm_QEC_Locality_BGKLSeparatorSplit_left_outerBoundary_subset
-- name    : QEC.Locality.BGKLSeparatorSplit.left_outerBoundary_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:33:59.429198+00:00
-- url     : https://prove2.me/theorems/e27ccce9-50b8-46dd-b3bd-e46e3f1fc8ea
-- title:
--   BGKLSeparator Split: left outer Boundary subset
-- statement:
--   A left child's outer boundary lies in the parent's boundary or separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L192-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L192-L217

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

theorem QEC.Locality.BGKLSeparatorSplit.left_outerBoundary_subset
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices) :
    fixedGeneratorOuterBoundaryFinset P split.left ⊆
      fixedGeneratorOuterBoundaryFinset P vertices ∪ split.separator := by sorry
