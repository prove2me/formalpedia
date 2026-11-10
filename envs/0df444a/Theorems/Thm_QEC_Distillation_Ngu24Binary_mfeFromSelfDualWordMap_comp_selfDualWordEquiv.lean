-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_mfeFromSelfDualWordMap_comp_selfDualWordEquiv
-- name    : QEC.Distillation.Ngu24Binary.mfeFromSelfDualWordMap_comp_selfDualWordEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:33:45.932235+00:00
-- url     : https://prove2.me/theorems/b5accf93-638d-489f-af07-a940c2f4a391
-- title:
--   Ngu24 Binary: mfe From Self Dual Word Map comp self Dual Word Equiv
-- statement:
--   The word-level basis change gives exactly the physical MFE already used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L61-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L61-L69

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
set_option maxRecDepth 2048

theorem QEC.Distillation.Ngu24Binary.mfeFromSelfDualWordMap_comp_selfDualWordEquiv :
    (mfeFromSelfDualWordMap J).comp (selfDualWordEquiv J).toLinearMap =
      physicalWordEmbedding J := by sorry
