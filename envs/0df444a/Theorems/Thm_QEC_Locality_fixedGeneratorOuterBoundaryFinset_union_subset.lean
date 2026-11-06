-- Prove2me | Theorems.Thm_QEC_Locality_fixedGeneratorOuterBoundaryFinset_union_subset
-- name    : QEC.Locality.fixedGeneratorOuterBoundaryFinset_union_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:34:22.670794+00:00
-- url     : https://prove2.me/theorems/9cfb1ad9-d51e-4770-9fd2-562c548ad194
-- title:
--   Locality: fixed Generator Outer Boundary Finset union subset
-- statement:
--   The boundary of a union is contained in the union of the two boundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L249-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L249-L266

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

theorem QEC.Locality.fixedGeneratorOuterBoundaryFinset_union_subset
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (left right : Finset ι) :
    fixedGeneratorOuterBoundaryFinset P (left ∪ right) ⊆
      fixedGeneratorOuterBoundaryFinset P left ∪
        fixedGeneratorOuterBoundaryFinset P right := by sorry
