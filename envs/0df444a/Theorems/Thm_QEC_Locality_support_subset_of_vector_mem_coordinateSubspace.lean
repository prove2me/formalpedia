-- Prove2me | Theorems.Thm_QEC_Locality_support_subset_of_vector_mem_coordinateSubspace
-- name    : QEC.Locality.support_subset_of_vector_mem_coordinateSubspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:31:59.719083+00:00
-- url     : https://prove2.me/theorems/d1eb8cbf-3fe6-471a-a63e-4e570d733713
-- title:
--   Locality: support subset of vector mem coordinate Subspace
-- statement:
--   Coordinate-subspace membership is the vector form of finite support containment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L76-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L76-L90

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.support_subset_of_vector_mem_coordinateSubspace
    (R : Finset ι) (E : Binary ι) (hE : E.vector ∈ coordinateSubspace R) :
    support E ⊆ R := by sorry
