-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_exists_monic_originalHecke_annihilator
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_exists_monic_originalHecke_annihilator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:50:56.460651+00:00
-- url     : https://prove2.me/theorems/bf880128-6f81-4234-aae7-1c616e019676
-- title:
--   Tanner Lifted Product: lps Theta exists monic original Hecke annihilator
-- statement:
--   A derived integer polynomial annihilates the original nonzero theta cusp form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L18-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L18-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_exists_monic_originalHecke_annihilator
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hq4 : q%4=1)
    (hNp : p.Coprime ((4*q)^2)) :
    ∃ P : ℤ[X], P.Monic ∧
      (aeval (lpsCuspHeckeLinearMap ((4*q)^2) p hNp) (P.map (Int.castRingHom ℂ)))
        (lpsThetaCuspidalRemainder q hq4) = 0 := by sorry
