-- Prove2me | Theorems.Thm_QEC_Coding_SmallSetExpansion_highDegree_card_bound_of_density_gap
-- name    : QEC.Coding.SmallSetExpansion.highDegree_card_bound_of_density_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:34:50.853181+00:00
-- url     : https://prove2.me/theorems/40247349-0992-4c89-bf65-176eecb1ac9b
-- title:
--   Small Set Expansion: high Degree card bound of density gap
-- statement:
--   A specified positive gap after the uniform-density contribution gives
--   the sharp squared gap bound, without the factor-four half-gap relaxation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/MixingDegree.lean#L54-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/MixingDegree.lean#L54-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u} [Fintype V] [Nonempty V]

theorem QEC.Coding.SmallSetExpansion.highDegree_card_bound_of_density_gap
    (M : WeightedGraph V) (degree : Nat) (spectral threshold gap : ℝ)
    (hSpectral : 0 ≤ spectral) (hGap : 0 < gap)
    (hMixing : HasExpanderMixingBound M degree spectral)
    (S T : Finset V)
    (hDegree : threshold * S.card ≤ (crossCount M S T : ℝ))
    (hDensity : (degree : ℝ) * T.card + gap * Fintype.card V ≤
      threshold * Fintype.card V) :
    gap ^ 2 * S.card ≤ spectral ^ 2 * T.card := by sorry
