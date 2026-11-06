-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_card_generatedGroupElement_eq_two_pow_generatorRank
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.card_generatedGroupElement_eq_two_pow_generatorRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:25.790556+00:00
-- url     : https://prove2.me/theorems/b93876c2-2afb-48af-935d-9f80ccaf7e08
-- title:
--   Binary Stabilizer Presentation: card generated Group Element eq two pow generator Rank
-- statement:
--   The faithful source-valid generated group has cardinality `2^r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L246-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L246-L254

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.card_generatedGroupElement_eq_two_pow_generatorRank
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    Fintype.card P.code.1.GeneratedGroupElement = 2 ^ P.generatorRank := by sorry
