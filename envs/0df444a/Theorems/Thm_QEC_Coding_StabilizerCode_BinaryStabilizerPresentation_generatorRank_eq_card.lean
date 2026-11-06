-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_generatorRank_eq_card
-- name    : QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.generatorRank_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:42:47.775144+00:00
-- url     : https://prove2.me/theorems/d17f7f2c-d48b-40aa-a5af-3f628496794b
-- title:
--   Binary Stabilizer Presentation: generator Rank eq card
-- statement:
--   Independence proves that the generator rank is the number of fixed generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L124-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Parameters.lean#L124-L128

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

theorem QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.generatorRank_eq_card
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    P.generatorRank = Fintype.card κ := by sorry
