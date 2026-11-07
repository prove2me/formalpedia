-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_encodedDimension_eq
-- name    : QEC.Coding.QuantumTanner.Data.encodedDimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:55:28.392567+00:00
-- url     : https://prove2.me/theorems/43a7b1d3-1764-4976-83a0-458058ad69b4
-- title:
--   Data: encoded Dimension eq
-- statement:
--   The Data construction uses the encoded Dimension eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L388-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L388-L392

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.encodedDimension_eq (D : Data G A B Square XBasis ZBasis) :
    D.encodedDimension =
      Dimension D.chainComplex.middleCycleCode -
        Dimension D.chainComplex.middleBoundaryCode := by sorry
