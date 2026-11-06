-- Prove2me | Theorems.Thm_QEC_Locality_profileSeparator_child_card_lt
-- name    : QEC.Locality.profileSeparator_child_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:27.630381+00:00
-- url     : https://prove2.me/theorems/3d2d4875-2dff-49de-984d-40505cf50943
-- title:
--   Locality: profile Separator child card lt
-- statement:
--   The profile threshold turns a minimum balanced separator into strict edge-region descent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L135-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L135-L150

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.profileSeparator_child_card_lt
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1)
    {vertices left separator : Finset ι}
    (hvertices : 1 ≤ vertices.card)
    (hscale : profileSeparatorThreshold beta exponent ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
    (hbalanced : 3 * left.card ≤ 2 * vertices.card) :
    left.card + separator.card < vertices.card := by sorry
