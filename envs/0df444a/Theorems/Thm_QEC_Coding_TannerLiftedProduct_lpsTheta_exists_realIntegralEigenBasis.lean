-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTheta_exists_realIntegralEigenBasis
-- name    : QEC.Coding.TannerLiftedProduct.lpsTheta_exists_realIntegralEigenBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:52:52.852329+00:00
-- url     : https://prove2.me/theorems/1dd349e4-c9ab-4c5a-8097-f558ef2a73e1
-- title:
--   Tanner Lifted Product: lps Theta exists real Integral Eigen Basis
-- statement:
--   The actual derived real spectrum on the active original theta support is algebraically integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L68-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralSpectrum.lean#L68-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralSpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsTheta_exists_realIntegralEigenBasis (q p : ℕ) [Fact q.Prime] [Fact p.Prime]
    (hq4 : q%4=1) (hNp : p.Coprime ((4*q)^2)) :
    ∃b : Module.Basis (Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))) ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2),
    ∃eigenvalue : Fin (Module.finrank ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2))→ℝ,
    (∀i,lpsCuspHeckeLinearMap ((4*q)^2) p hNp (b i)=(eigenvalue i:ℂ) • b i) ∧
    ∀i,b.repr (lpsThetaCuspidalRemainder q hq4) i≠0 → IsIntegral ℤ (eigenvalue i:ℂ) := by sorry
