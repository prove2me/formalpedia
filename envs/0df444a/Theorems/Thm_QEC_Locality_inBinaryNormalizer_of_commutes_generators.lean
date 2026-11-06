-- Prove2me | Theorems.Thm_QEC_Locality_inBinaryNormalizer_of_commutes_generators
-- name    : QEC.Locality.inBinaryNormalizer_of_commutes_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:32:34.29392+00:00
-- url     : https://prove2.me/theorems/647a6f6d-d15e-4102-b779-51725b3d1d36
-- title:
--   Locality: in Binary Normalizer of commutes generators
-- statement:
--   The Locality construction uses the in Binary Normalizer of commutes generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L292-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/CorrectableRegionClosure.lean#L292-L303

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

theorem QEC.Locality.inBinaryNormalizer_of_commutes_generators
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j : κ, Commutes E (P.generators j)) :
    P.code.1.InBinaryNormalizer E := by sorry
