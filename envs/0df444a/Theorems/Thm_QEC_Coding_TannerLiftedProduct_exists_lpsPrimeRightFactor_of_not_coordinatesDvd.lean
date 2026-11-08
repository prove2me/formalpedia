-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_lpsPrimeRightFactor_of_not_coordinatesDvd
-- name    : QEC.Coding.TannerLiftedProduct.exists_lpsPrimeRightFactor_of_not_coordinatesDvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:51:06.433907+00:00
-- url     : https://prove2.me/theorems/15a9740d-df82-47a3-8da4-2c88729ad710
-- title:
--   Tanner Lifted Product: exists lps Prime Right Factor of not coordinates Dvd
-- statement:
--   Every primitive integral quaternion whose norm is divisible by `p` has
--   a normalized norm-`p` right factor.  The quotient is integral because the
--   product with the conjugate factor vanishes modulo `p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L410-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L410-L443

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.exists_lpsPrimeRightFactor_of_not_coordinatesDvd
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    ∃ beta : LPSGeneratorIndex p,
      (t * beta.1.conj).CoordinatesDvd (p : ℤ) := by sorry
