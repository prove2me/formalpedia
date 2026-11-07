-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_heavyDegree_le_twice_localWeight
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_heavyDegree_le_twice_localWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:52:51.114613+00:00
-- url     : https://prove2.me/theorems/a97d565c-2aa8-4aac-b15b-8b8b70b1d620
-- title:
--   Left Right Cayley Square Complex: cutoff mul heavy Degree le twice local Weight
-- statement:
--   Heavy incidences at a vertex are paid for by twice its actual local weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L273-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L273-L295

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_heavyDegree_le_twice_localWeight
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (g : G) :
    cutoff * (∑ h : G, X.heavyUnionGraph side x cutoff g h) ≤
      2 * HammingWeight (X.localRestriction (g, side) x) := by sorry
