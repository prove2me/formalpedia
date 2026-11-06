-- Prove2me | Theorems.Thm_QEC_Locality_minimumSeparator_card_le_profilePowerCeil
-- name    : QEC.Locality.minimumSeparator_card_le_profilePowerCeil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:30:02.345316+00:00
-- url     : https://prove2.me/theorems/856c43a4-d624-489d-807b-b466aa44aace
-- title:
--   Locality: minimum Separator card le profile Power Ceil
-- statement:
--   Natural-ceiling form of the same exact profile-power bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L294-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L294-L304

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.minimumSeparator_card_le_profilePowerCeil
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (vertices separator : Finset ι)
    (hvertices : 1 ≤ vertices.card)
    (hminimum :
      separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices) :
    separator.card ≤ Nat.ceil (beta * Real.rpow vertices.card exponent) := by sorry
