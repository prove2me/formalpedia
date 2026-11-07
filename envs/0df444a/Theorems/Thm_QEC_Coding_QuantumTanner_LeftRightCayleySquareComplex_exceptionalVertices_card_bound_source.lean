-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptionalVertices_card_bound_source
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:12:07.561982+00:00
-- url     : https://prove2.me/theorems/24025ee1-b7fe-4428-8daa-36f3cabcc191
-- title:
--   Left Right Cayley Square Complex: exceptional Vertices card bound source
-- statement:
--   The source's `64 / Delta^(1 - 2 epsilon)` exceptional-vertex estimate,
--   with the real threshold interpreted by its exact integer ceiling.
--   The mixing assumption concerns this complex's actual square multigraph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExceptionalVertices.lean#L49-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExceptionalVertices.lean#L49-L97

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_source
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (Delta : Nat) (epsilon : ℝ)
    (hDelta : 0 < Delta) (hA : Fintype.card A = Delta) (hB : Fintype.card B = Delta)
    (hMixing : HasExpanderMixingBound (X.squareGraph side) (Delta * Delta)
      (4 * (Delta : ℝ)))
    (hSmall : ((X.activeVerticesOnSide side x).card : ℝ) ≤
      Fintype.card G / (4 * (Delta : ℝ) ^ (1 / 2 + epsilon))) :
    ((X.exceptionalVerticesOnSide side x
      (Nat.ceil ((Delta : ℝ) ^ (3 / 2 - epsilon)))).card : ℝ) ≤
      64 / (Delta : ℝ) ^ (1 - 2 * epsilon) *
        (X.activeVerticesOnSide side x).card := by sorry
