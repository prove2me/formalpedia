-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_natCard_lpsProjectiveLine
-- name    : QEC.Coding.TannerLiftedProduct.natCard_lpsProjectiveLine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:48:05.046203+00:00
-- url     : https://prove2.me/theorems/5e236f6d-cffe-45cb-b0cb-ae1cba26fdc7
-- title:
--   Tanner Lifted Product: nat Card lps Projective Line
-- statement:
--   The projective line over `ZMod p` has `p+1` points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L377-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L377-L383

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.natCard_lpsProjectiveLine [Fact p.Prime] :
    Nat.card (ℙ (ZMod p) (Fin 2 → ZMod p)) = p + 1 := by sorry
