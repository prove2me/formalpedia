-- Prove2me | Theorems.Thm_QEC_Locality_commutes_restrictBinaryTo_generator_of_no_cross_edge
-- name    : QEC.Locality.commutes_restrictBinaryTo_generator_of_no_cross_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:42.384208+00:00
-- url     : https://prove2.me/theorems/4d38291d-7d76-4a71-8d3f-28d00035d512
-- title:
--   Locality: commutes restrict Binary To generator of no cross edge
-- statement:
--   The Locality construction uses the commutes restrict Binary To generator of no cross edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L305-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L305-L337

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

theorem QEC.Locality.commutes_restrictBinaryTo_generator_of_no_cross_edge
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : Finset ι) (E : Binary ι)
    (hdisjoint : Disjoint A B)
    (hnoCross : P.fixedGeneratorNoCrossEdge (A : Set ι) (B : Set ι))
    (hdecompose : E.vector =
      (restrictBinaryTo A E).vector + (restrictBinaryTo B E).vector)
    (j : κ) (hE : Commutes E (P.generators j)) :
    Commutes (restrictBinaryTo A E) (P.generators j) := by sorry
