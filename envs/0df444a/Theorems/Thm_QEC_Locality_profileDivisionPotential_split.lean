-- Prove2me | Theorems.Thm_QEC_Locality_profileDivisionPotential_split
-- name    : QEC.Locality.profileDivisionPotential_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:19.196245+00:00
-- url     : https://prove2.me/theorems/5b543839-6037-4e5a-ad68-a74de0f21f5d
-- title:
--   Locality: profile Division Potential split
-- statement:
--   One retained separator split is paid for by the drop in the graph-uniform potential.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L274-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/DivisionPotential.lean#L274-L380

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality

theorem QEC.Locality.profileDivisionPotential_split
    {beta exponent : ℝ} {r parent left right separator : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hparent : 0 < parent)
    (hsum : left + right = parent + separator)
    (hleftLower : parent + separator ≤ 4 * left)
    (hleftUpper : 4 * left ≤ 3 * (parent + separator))
    (hseparator : (separator : ℝ) ≤ beta * (parent : ℝ) ^ exponent)
    (hscale :
      profileDivisionPotentialCoefficient beta exponent *
          (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) ≤ 1) :
    3 * separator + profileDivisionPotential beta exponent r left +
        profileDivisionPotential beta exponent r right ≤
      profileDivisionPotential beta exponent r parent := by sorry
