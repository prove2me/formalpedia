-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_card_bound_of_density_gap
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_of_density_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:32:09.253951+00:00
-- url     : https://prove2.me/theorems/cb557d9e-8b6b-4461-9888-7828ae3c7e8e
-- title:
--   Left Right Cayley Square Complex: opposite Heavy Set card bound of density gap
-- statement:
--   The actual opposite set obeys the finite high-degree mixing bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L422-L437
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L422-L437

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_of_density_gap
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (spectral gap : ℝ) (hSpectral : 0 ≤ spectral) (hGap : 0 < gap)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (cutoff : ℝ) * Fintype.card G) :
    gap ^ 2 * (X.oppositeHeavySet side x cutoff normal).card ≤
      spectral ^ 2 * (X.activeVerticesOnSide side x).card := by sorry
