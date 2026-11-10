-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_basis
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:40:32.81019+00:00
-- url     : https://prove2.me/theorems/3892fcc9-ec45-47d3-b426-07be741b3b02
-- title:
--   Ngu24 Binary: binary Encoded Code basis
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L93-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L93-L102

import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_3142684436_53

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_basis (i : Nat) (u : Fin (f256MultiplicationLogicalCount i) → ZMod 2) :
    (binaryEncodedCode i).encode (EuclideanSpace.basisFun _ Complex u) =
      physicalIsometry (f256SourceInput i).PivotComplement
        ((f256SourceInput i).shortenedCosetKet
          (logicalWordEmbedding (Fin (f256MultiplicationLogicalCount i)) u)) := by sorry
