-- Prove2me | Theorems.Thm_QEC_Locality_AssumedBGKLMeasuredProfilePowerUpperBound_edgeRestricted
-- name    : QEC.Locality.AssumedBGKLMeasuredProfilePowerUpperBound.edgeRestricted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:11:10.473669+00:00
-- url     : https://prove2.me/theorems/daf08bcc-d2d7-495d-9978-934c1ebb4ab2
-- title:
--   Assumed BGKLMeasured Profile Power Upper Bound: edge Restricted
-- statement:
--   The graph-uniform profile hypothesis is inherited by every finite edge subproblem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L52-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Quantitative.lean#L52-L62

import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.AssumedBGKLMeasuredProfilePowerUpperBound.edgeRestricted
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (edges : Finset (ι × ι)) :
    AssumedBGKLMeasuredProfilePowerUpperBound
      (edgeRestrictedGraph G edges) beta exponent := by sorry
