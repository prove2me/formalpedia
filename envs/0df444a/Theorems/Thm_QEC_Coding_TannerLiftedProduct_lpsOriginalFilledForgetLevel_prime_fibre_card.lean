-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_prime_fibre_card
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_prime_fibre_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:40:48.415972+00:00
-- url     : https://prove2.me/theorems/097e2e06-669a-4ddb-b258-b1b3e5e9dd19
-- title:
--   Tanner Lifted Product: lps Original Filled Forget Level prime fibre card
-- statement:
--   Every genuine interior point has p+1 preimages under the actual original filled map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelFibres.lean#L233-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelFibres.lean#L233-L242

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_prime_fibre_card
    (N p : ℕ) [Fact p.Prime] (hNp : p.Coprime N) (hN : 4 ∣ N)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Nat.card {x : LPSOriginalFilledCurve (N*p) |
      lpsOriginalFilledForgetLevel N (N*p) (dvd_mul_right N p) x = Sum.inl y} = p+1 := by sorry
