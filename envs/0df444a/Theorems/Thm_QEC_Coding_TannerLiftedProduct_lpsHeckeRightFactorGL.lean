-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeRightFactorGL
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeRightFactorGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:46.99173+00:00
-- url     : https://prove2.me/theorems/3baccd4e-c344-41a8-8d39-d68f2fe48cfa
-- title:
--   Tanner Lifted Product: lps Hecke Right Factor GL
-- statement:
--   Integral factor equality transfers to the actual GL products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L336-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L336-L348

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeRightFactorGL (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i j : Option (Fin p)) (γ δ : SL(2,ℤ))
    (h : lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j) :
    lpsHeckeUpperGL R p i*Matrix.SpecialLinearGroup.mapGL R γ=
      Matrix.SpecialLinearGroup.mapGL R δ*lpsHeckeUpperGL R p j := by sorry
