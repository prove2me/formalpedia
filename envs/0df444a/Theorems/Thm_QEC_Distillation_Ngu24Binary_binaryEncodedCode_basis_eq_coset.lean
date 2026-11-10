-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_basis_eq_coset
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_basis_eq_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:49:15.238557+00:00
-- url     : https://prove2.me/theorems/2d735ef2-d42d-4496-990e-1be362c2cb5f
-- title:
--   Ngu24 Binary: binary Encoded Code basis eq coset
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code basis eq coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L148-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L148-L162

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_basis_eq_coset (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) = binaryCosetKet i u := by sorry
