-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_card_bound_source
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:08:56.90831+00:00
-- url     : https://prove2.me/theorems/6c9a4459-03eb-4585-b7cf-56391d5d85ce
-- title:
--   Left Right Cayley Square Complex: opposite Heavy Set card bound source
-- statement:
--   The `64/(delta^2 Delta)` constant in [LZ22, equation eqn:T], after
--   the uniform-density term is absorbed into the explicit half-distance gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L441-L464
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L441-L464

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_source
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (Delta : Nat) (hDelta : 0 < Delta) (delta : ℝ) (hDeltaDistance : 0 < delta)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) (4 * Real.sqrt Delta))
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card +
        (delta * Delta / 2) * Fintype.card G ≤ (cutoff : ℝ) * Fintype.card G) :
    (X.oppositeHeavySet side x cutoff normal).card ≤
      64 / (delta ^ 2 * Delta) * (X.activeVerticesOnSide side x).card := by sorry
