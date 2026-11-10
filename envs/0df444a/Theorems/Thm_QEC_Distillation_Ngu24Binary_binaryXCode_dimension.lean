-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryXCode_dimension
-- name    : QEC.Distillation.Ngu24Binary.binaryXCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:47:39.798713+00:00
-- url     : https://prove2.me/theorems/000fa1e5-3574-4e98-9395-8c8d81407d67
-- title:
--   Ngu24 Binary: binary XCode dimension
-- statement:
--   The Ngu24 Binary construction uses the binary XCode dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L104-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L104-L106

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

theorem QEC.Distillation.Ngu24Binary.binaryXCode_dimension (i : Nat) :
    Dimension (binaryXCode i) = Module.finrank (ZMod 2) (f256SourceInput i).H0 := by sorry
