-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_complement_separates
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_complement_separates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:21:10.456191+00:00
-- url     : https://prove2.me/theorems/4660658b-101e-4be6-bb13-b34d100c7b27
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input complement separates
-- statement:
--   Small-region erasure cannot identify two different physical coset summands.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L54-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L54-L89

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureInterpolation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureInput
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CosetDetectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Semantics
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_complement_separates (i : ℕ)
    (S : Finset (f256SourceInput i).PivotComplement)
    (hS : S.card < (f256GarciaStichtenothLength i + 4) / 5 -
      f256MultiplicationLogicalCount i)
    (u v : Fin (f256MultiplicationLogicalCount i) → F256)
    (h k : (f256SourceInput i).H0)
    (hsame : ∀ j, j ∉ S → (f256SourceInput i).shortenedCosetLabel u h j =
      (f256SourceInput i).shortenedCosetLabel v k j) :
    u = v ∧ h = k := by sorry
