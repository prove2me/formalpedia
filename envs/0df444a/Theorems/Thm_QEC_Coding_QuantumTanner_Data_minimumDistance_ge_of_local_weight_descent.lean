-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_Data_minimumDistance_ge_of_local_weight_descent
-- name    : QEC.Coding.QuantumTanner.Data.minimumDistance_ge_of_local_weight_descent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:24:02.961517+00:00
-- url     : https://prove2.me/theorems/06b3a7a1-58b4-415a-8719-be4ae624924c
-- title:
--   Data: minimum Distance ge of local weight descent
-- statement:
--   The two local reduction statements imply a lower bound for the actual
--   Quantum Tanner CSS minimum. Their geometric existence is a separate obligation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L361-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L361-L394

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.Data
variable {G A B Square XBasis ZBasis : Type v}
  [Group G] [Fintype G] [Fintype A] [Fintype B] [Fintype Square]
  [Fintype XBasis] [Fintype ZBasis]

theorem QEC.Coding.QuantumTanner.Data.minimumDistance_ge_of_local_weight_descent
    (D : Data G A B Square XBasis ZBasis) (threshold : Nat)
    (hreduceX : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.middleBoundaryCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA.dual D.codeB.dual).carrier ∧
        HammingWeight (D.complex.localRestriction (g, true) x + c) <
          HammingWeight (D.complex.localRestriction (g, true) x))
    (hreduceZ : ∀ x : Word (ZMod 2) Square,
      x ∈ D.chainComplex.firstCoboundaryCheckCode.dual.carrier → x ≠ 0 →
      HammingWeight x < threshold →
      ∃ g : G, ∃ c : Word (ZMod 2) (A × B),
        c ∈ (tensorCode D.codeA D.codeB).carrier ∧
        HammingWeight (D.complex.localRestriction (g, false) x + c) <
          HammingWeight (D.complex.localRestriction (g, false) x))
    {distance : Nat}
    (hmin : AlgebraicCSSMinimumDistance D.chainComplex.firstCoboundaryCheckCode
      D.chainComplex.middleBoundaryCode distance) : threshold ≤ distance := by sorry
