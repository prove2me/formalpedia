-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_fixed_X
-- name    : QEC.Distillation.Ngu24Binary.binaryCosetKet_fixed_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:49:14.607546+00:00
-- url     : https://prove2.me/theorems/97b8ba98-1093-4267-b85e-625e20166324
-- title:
--   Ngu24 Binary: binary Coset Ket fixed X
-- statement:
--   The Ngu24 Binary construction uses the binary Coset Ket fixed X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L164-L177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L164-L177

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

theorem QEC.Distillation.Ngu24Binary.binaryCosetKet_fixed_X (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) (k : (f256SourceInput i).H0) :
    PauliSymplectic.toQubitOperator (PauliSymplectic.cssXCheck (binaryKernelWordMap i k))
      (binaryCosetKet i u) = binaryCosetKet i u := by sorry
