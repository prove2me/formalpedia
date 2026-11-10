-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryAmbientCode_dimension
-- name    : QEC.Distillation.Ngu24Binary.binaryAmbientCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:48:21.617074+00:00
-- url     : https://prove2.me/theorems/a23aa811-a392-486c-b97c-9c48aa8ff995
-- title:
--   Ngu24 Binary: binary Ambient Code dimension
-- statement:
--   The Ngu24 Binary construction uses the binary Ambient Code dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L97-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L97-L102

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24Binary.binaryAmbientCode_dimension (i : Nat) :
    Dimension (binaryAmbientCode i) = f256MultiplicationLogicalCount i +
      Module.finrank (ZMod 2) (f256SourceInput i).H0 := by sorry
