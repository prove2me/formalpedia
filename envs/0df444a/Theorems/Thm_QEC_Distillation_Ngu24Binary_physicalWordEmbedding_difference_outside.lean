-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalWordEmbedding_difference_outside
-- name    : QEC.Distillation.Ngu24Binary.physicalWordEmbedding_difference_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:41:52.642734+00:00
-- url     : https://prove2.me/theorems/45d7b471-aacc-4d8d-84ab-fc90862ba687
-- title:
--   Ngu24 Binary: physical Word Embedding difference outside
-- statement:
--   The Ngu24 Binary construction uses the physical Word Embedding difference outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L22-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryDistance.lean#L22-L32

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {J : Type} [DecidableEq J]

theorem QEC.Distillation.Ngu24Binary.physicalWordEmbedding_difference_outside (S : Finset (J × Fin 512))
    (x y : J → F256) (h : ∃ j, j ∉ S.image Prod.fst ∧ x j ≠ y j) :
    ∃ t, t ∉ S ∧ physicalWordEmbedding J x t ≠ physicalWordEmbedding J y t := by sorry
