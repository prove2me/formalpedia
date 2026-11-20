-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaPeterssonPairing_norm_sq_le_mass_mul_mass
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaPeterssonPairing_norm_sq_le_mass_mul_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:34:48.922013+00:00
-- url     : https://prove2.me/theorems/9ccc21b4-76a2-46cb-a9b9-9bb4718a461d
-- title:
--   Tanner Lifted Product: lps Theta Petersson Pairing norm sq le mass mul mass
-- statement:
--   The actual theta pairing is bounded by its genuine mass and the other form's square integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L63-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaPeterssonPositive.lean#L63-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaPeterssonPairing_norm_sq_le_mass_mul_mass (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (g : CuspForm (CongruenceSubgroup.Gamma0 ((4*q)^2) : Subgroup (GL (Fin 2) ℝ)) 2) :
    let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
    ‖lpsCuspPeterssonPairing ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) g‖^2 ≤
      lpsThetaRankinMass q hq4*(∫τ in ModularGroup.fd,lpsCuspPeterssonDensity ((4*q)^2) g τ) := by sorry
