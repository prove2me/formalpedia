-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedCosetLabel_eq
-- name    : QEC.Distillation.Ngu24Binary.binaryTaggedCosetLabel_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:54:31.988285+00:00
-- url     : https://prove2.me/theorems/3a80c4e1-7436-4fe3-a632-e6fecd0ebbd2
-- title:
--   Ngu24 Binary: binary Tagged Coset Label eq
-- statement:
--   The Ngu24 Binary construction uses the binary Tagged Coset Label eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L113-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTaggedEncoding.lean#L113-L123

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance 2000] QEC.Distillation.Ngu24Binary.binaryTaggedFinDecidableEq

theorem QEC.Distillation.Ngu24Binary.binaryTaggedCosetLabel_eq (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (h : ThreeCopyTag → (f256SourceInput i).H0) :
    taggedPhysicalWordEmbedding (f256SourceInput i).PivotComplement
      (taggedShortenedCosetLabel (f256SourceInput i)
        (logicalWordEmbedding (ThreeCopyTag × Fin (f256MultiplicationLogicalCount i)) u) h) =
      binaryTaggedCosetLabel i u h := by sorry
