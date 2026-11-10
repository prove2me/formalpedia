-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryKernelWordMap_injective
-- name    : QEC.Distillation.Ngu24Binary.binaryKernelWordMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:48:47.171634+00:00
-- url     : https://prove2.me/theorems/ca71dc9e-650d-4df5-bfe1-fb996494a6e3
-- title:
--   Ngu24 Binary: binary Kernel Word Map injective
-- statement:
--   The Ngu24 Binary construction uses the binary Kernel Word Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L69-L73

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

theorem QEC.Distillation.Ngu24Binary.binaryKernelWordMap_injective (i : Nat) : Function.Injective (binaryKernelWordMap i) := by sorry
