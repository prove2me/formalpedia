-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:39.894798+00:00
-- url     : https://prove2.me/theorems/7f38d0c5-4ea1-4448-a71d-b79026eeab94
-- title:
--   Tanner Lifted Product: lps Hecke Upper GL det
-- statement:
--   The GL representative has determinant p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L321-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L321-L326

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_det (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i).det.val=(p:R) := by sorry
