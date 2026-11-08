-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_f256SourceInput_cosetLabel_mem_punctured
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_cosetLabel_mem_punctured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:22.79371+00:00
-- url     : https://prove2.me/theorems/5e789249-016c-4c3f-99f4-dcd91774448b
-- title:
--   Ngu24 Multiplicative CSS: f256 Source Input coset Label mem punctured
-- statement:
--   Every physical coset summand lies in the actual punctured evaluation code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L44-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureDistance.lean#L44-L51

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.f256SourceInput_cosetLabel_mem_punctured (i : ℕ)
    (u : Fin (f256MultiplicationLogicalCount i) → F256) (h : (f256SourceInput i).H0) :
    (f256SourceInput i).shortenedCosetLabel u h ∈
      (f256PuncturedMultiplicationCode i).carrier := by sorry
