-- Prove2me | Theorems.Thm_QEC_Locality_profileDivisionPotential_le_linear
-- name    : QEC.Locality.profileDivisionPotential_le_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:24.117645+00:00
-- url     : https://prove2.me/theorems/182795fc-57ce-45bb-af4a-3425802080b9
-- title:
--   Locality: profile Division Potential le linear
-- statement:
--   Dropping the nonnegative concave term gives the useful linear potential bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L228-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L228-L240

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality

theorem QEC.Locality.profileDivisionPotential_le_linear
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent ≤
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
          (1 / 4 : ℝ) ^ (1 - exponent)) := by sorry
