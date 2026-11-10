-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetWordMap_injective
-- name    : QEC.Distillation.Ngu24Binary.binaryCosetWordMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:50:44.761075+00:00
-- url     : https://prove2.me/theorems/06562e59-0f58-46e5-af50-bbc56d53d8de
-- title:
--   Ngu24 Binary: binary Coset Word Map injective
-- statement:
--   The Ngu24 Binary construction uses the binary Coset Word Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L59-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L59-L67

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

theorem QEC.Distillation.Ngu24Binary.binaryCosetWordMap_injective (i : Nat) : Function.Injective (binaryCosetWordMap i) := by sorry
