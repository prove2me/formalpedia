-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLambertTerm_eq_X_pow_mul_geometric
-- name    : QEC.Coding.TannerLiftedProduct.jacobiLambertTerm_eq_X_pow_mul_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:35:43.078236+00:00
-- url     : https://prove2.me/theorems/9002a67b-ec2b-4309-b55d-24b88142da2a
-- title:
--   Tanner Lifted Product: jacobi Lambert Term eq X pow mul geometric
-- statement:
--   The Tanner Lifted Product construction uses the jacobi Lambert Term eq X pow mul geometric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L116-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiFourSquareIdentity.lean#L116-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.jacobiLambertTerm_eq_X_pow_mul_geometric {d : ℕ} (hd : d ≠ 0) :
    jacobiLambertTerm d =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d *
        jacobiGeometricSeries.subst (PowerSeries.X ^ d) := by sorry
