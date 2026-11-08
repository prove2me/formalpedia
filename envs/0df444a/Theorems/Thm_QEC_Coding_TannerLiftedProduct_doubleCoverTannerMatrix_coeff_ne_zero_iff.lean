-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_doubleCoverTannerMatrix_coeff_ne_zero_iff
-- name    : QEC.Coding.TannerLiftedProduct.doubleCoverTannerMatrix_coeff_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:24.661317+00:00
-- url     : https://prove2.me/theorems/50cc874f-fd7d-4ece-acfe-36b820f0fe0d
-- title:
--   Tanner Lifted Product: double Cover Tanner Matrix coeff ne zero iff
-- statement:
--   A Tanner entry has a nonzero coefficient at exactly its selected voltage,
--   provided the corresponding local-matrix coefficient is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L69-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L69-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R]

theorem QEC.Coding.TannerLiftedProduct.doubleCoverTannerMatrix_coeff_ne_zero_iff
    (label : W → G) (h : Matrix R W F)
    (ir : Fin 2 × R) (j : W) (g : G) :
  (doubleCoverTannerMatrix label h ir j).coeff g ≠ 0 ↔
      g = doubleCoverVoltage label ir.1 j ∧ h ir.2 j ≠ 0 := by sorry
