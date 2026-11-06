-- Prove2me | Theorems.Thm_QEC_Locality_restrictBinaryTo_vector_add_of_support_subset_union
-- name    : QEC.Locality.restrictBinaryTo_vector_add_of_support_subset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:13.881194+00:00
-- url     : https://prove2.me/theorems/fae45daa-f4b0-4684-98ab-e40ade7af7d2
-- title:
--   Locality: restrict Binary To vector add of support subset union
-- statement:
--   Restriction to two disjoint regions recombines every Pauli supported on their union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L121-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L121-L178

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

theorem QEC.Locality.restrictBinaryTo_vector_add_of_support_subset_union
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B) (hsupport : support E ⊆ A ∪ B) :
    E.vector = (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector := by sorry
