-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_exists_minimumDistance_of_encodedDimension_pos
-- name    : QEC.Coding.QuantumTanner.Data.exists_minimumDistance_of_encodedDimension_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:01:46.232195+00:00
-- url     : https://prove2.me/theorems/a0c593d8-e91a-489b-93cf-1f0df18affec
-- title:
--   Data: exists minimum Distance of encoded Dimension pos
-- statement:
--   Positive middle homology gives an actual nontrivial logical word and
--   hence an attained algebraic CSS minimum; attainment is not assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L49-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Parameters.lean#L49-L70

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ExpandingDistance
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.Data
open Classical
universe v
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.exists_minimumDistance_of_encodedDimension_pos
    (D : Data G A B Square XBasis ZBasis) (hPositive : 0 < D.encodedDimension) :
    ∃ distance : Nat, AlgebraicCSSMinimumDistance
      D.chainComplex.firstCoboundaryCheckCode D.chainComplex.middleBoundaryCode distance := by sorry
