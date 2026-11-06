-- Prove2me | Theorems.Thm_QEC_Locality_profileDivisionPotential_nonneg
-- name    : QEC.Locality.profileDivisionPotential_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:41.323987+00:00
-- url     : https://prove2.me/theorems/1c3c1d98-d21d-477c-a763-0ead2465c56f
-- title:
--   Locality: profile Division Potential nonneg
-- statement:
--   The retained potential is nonnegative once the parent is at least one quarter of `r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L193-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L193-L211

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality

theorem QEC.Locality.profileDivisionPotential_nonneg
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hlower : r ≤ 4 * parent) :
    0 ≤ profileDivisionPotential beta exponent r parent := by sorry
