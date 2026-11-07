-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_crossCount_le_linear_of_card_ratio
-- name    : QEC.Coding.SmallSetExpansion.crossCount_le_linear_of_card_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:35:11.21126+00:00
-- url     : https://prove2.me/theorems/f00c250d-b1bd-4a04-b428-d01167d1ee4e
-- title:
--   Small Set Expansion: cross Count le linear of card ratio
-- statement:
--   If the bad set is a small fraction of a set whose size is linear in
--   `T`, mixing gives a linear-in-`T` bound on actual bad incidences.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/MixingDegree.lean#L87-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/MixingDegree.lean#L87-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V] [Nonempty V]

theorem QEC.Coding.SmallSetExpansion.crossCount_le_linear_of_card_ratio
    (M : WeightedGraph V) (degree : Nat) (spectral fraction ratio uniformBudget : ℝ)
    (hSpectral : 0 ≤ spectral) (hFraction : 0 ≤ fraction) (hRatio : 0 ≤ ratio)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (bad S T : Finset V)
    (hBad : (bad.card : ℝ) ≤ fraction * S.card)
    (hRatioBound : (S.card : ℝ) ≤ ratio * T.card)
    (hMean : (degree : ℝ) * bad.card ≤ uniformBudget * Fintype.card V) :
    (crossCount M bad T : ℝ) ≤
      (uniformBudget + spectral * Real.sqrt (fraction * ratio)) * T.card := by sorry
