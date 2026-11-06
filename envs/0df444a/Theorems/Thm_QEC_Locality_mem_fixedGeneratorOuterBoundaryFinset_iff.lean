-- Prove2me | Theorems.Thm_QEC_Locality_mem_fixedGeneratorOuterBoundaryFinset_iff
-- name    : QEC.Locality.mem_fixedGeneratorOuterBoundaryFinset_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:23.025069+00:00
-- url     : https://prove2.me/theorems/dd50a31e-b33c-4b7a-ac21-f440a28aecc4
-- title:
--   Locality: mem fixed Generator Outer Boundary Finset iff
-- statement:
--   The Locality construction uses the mem fixed Generator Outer Boundary Finset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L131-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean#L131-L137

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

theorem QEC.Locality.mem_fixedGeneratorOuterBoundaryFinset_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) (q : ι) :
    q ∈ fixedGeneratorOuterBoundaryFinset P vertices ↔
      q ∈ P.fixedGeneratorOuterBoundary (vertices : Set ι) := by sorry
