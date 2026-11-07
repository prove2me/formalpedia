-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptionalVertices_card_bound_of_mixing
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_of_mixing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:33:56.649987+00:00
-- url     : https://prove2.me/theorems/82138853-c270-45d9-aca1-be3a3dc41c39
-- title:
--   Left Right Cayley Square Complex: exceptional Vertices card bound of mixing
-- statement:
--   Actual exceptional vertices obey the high-degree estimate when the full
--   same-side square multigraph has the stated mixing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExceptionalVertices.lean#L26-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/ExceptionalVertices.lean#L26-L44

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_of_mixing
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (threshold spectral : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : threshold ≤ cutoff)
    (hSpectral : 0 ≤ spectral)
    (hMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) spectral)
    (hSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ threshold * Fintype.card G) :
    threshold ^ 2 * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      4 * spectral ^ 2 * (X.activeVerticesOnSide side x).card := by sorry
