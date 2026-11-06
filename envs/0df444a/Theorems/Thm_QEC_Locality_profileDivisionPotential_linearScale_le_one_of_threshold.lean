-- Prove2me | Theorems.Thm_QEC_Locality_profileDivisionPotential_linearScale_le_one_of_threshold
-- name    : QEC.Locality.profileDivisionPotential_linearScale_le_one_of_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:23.423219+00:00
-- url     : https://prove2.me/theorems/0a50fcaa-08d2-48f5-9e11-6f85eabcda4d
-- title:
--   Locality: profile Division Potential linear Scale le one of threshold
-- statement:
--   The uniform division threshold makes the retained linear penalty at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L139-L190
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L139-L190

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality

theorem QEC.Locality.profileDivisionPotential_linearScale_le_one_of_threshold
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1)
    {r : Nat} (hthreshold : profileDivisionThreshold beta exponent ≤ r) :
    profileDivisionPotentialCoefficient beta exponent *
        (r : ℝ) ^ (exponent - 1) /
          (1 / 4 : ℝ) ^ (1 - exponent) ≤ 1 := by sorry
