-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetWordMap_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryCosetWordMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:48:13.449211+00:00
-- url     : https://prove2.me/theorems/fb2b46e9-5625-4e03-b89e-cfc1d4dab9ca
-- title:
--   Ngu24 Binary: binary Coset Word Map apply
-- statement:
--   The Ngu24 Binary construction uses the binary Coset Word Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L49-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L49-L57

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

theorem QEC.Distillation.Ngu24Binary.binaryCosetWordMap_apply (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) (h : (f256SourceInput i).H0) :
    binaryCosetWordMap i (u, h) = physicalWordEmbedding (f256SourceInput i).PivotComplement
      ((f256SourceInput i).shortenedCosetLabel
        (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u) h) := by sorry
