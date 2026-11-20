-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspFiniteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaCuspFiniteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:35:30.37307+00:00
-- url     : https://prove2.me/theorems/93aa4691-b009-487a-bc7e-b5b6a123a82f
-- title:
--   Tanner Lifted Product: lps Theta Cusp Finite Dimensional
-- statement:
--   The original LPS theta remainder lies in a proved finite-dimensional weight-two cusp space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFiniteDimension.lean#L19-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFiniteDimension.lean#L19-L23

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFiniteDimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsThetaCuspFiniteDimensional (p : ℕ) (a : LPSResiduePrime p) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 ((4*a.q)^2) :
      Subgroup (GL (Fin 2) ℝ)) 2) := by sorry
