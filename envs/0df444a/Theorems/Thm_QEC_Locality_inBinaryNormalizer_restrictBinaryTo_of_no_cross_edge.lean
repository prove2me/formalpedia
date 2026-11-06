-- Prove2me | Theorems.Thm_QEC_Locality_inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
-- name    : QEC.Locality.inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:00.603027+00:00
-- url     : https://prove2.me/theorems/7ca6b42d-cf3d-41b3-8a68-6c0b972c15d4
-- title:
--   Locality: in Binary Normalizer restrict Binary To of no cross edge
-- statement:
--   The Locality construction uses the in Binary Normalizer restrict Binary To of no cross edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L339-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L339-L367

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

theorem QEC.Locality.inBinaryNormalizer_restrictBinaryTo_of_no_cross_edge
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hnoCross : P.fixedGeneratorNoCrossEdge (A : Set ι) (B : Set ι))
    (hdecompose : E.vector =
      (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector)
    (hE : P.code.1.InBinaryNormalizer E) :
    P.code.1.InBinaryNormalizer (restrictBinaryTo A E) ∧
      P.code.1.InBinaryNormalizer (restrictBinaryTo B E) := by sorry
