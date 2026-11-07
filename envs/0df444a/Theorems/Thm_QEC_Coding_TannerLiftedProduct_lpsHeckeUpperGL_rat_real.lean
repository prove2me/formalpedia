-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_rat_real
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_rat_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:45.234049+00:00
-- url     : https://prove2.me/theorems/971c9aa8-e213-4f79-8e0e-926abd644bd1
-- title:
--   Tanner Lifted Product: lps Hecke Upper GL rat real
-- statement:
--   The real representative is the actual real image of its rational matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L329-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L329-L333

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_rat_real (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL ℚ p i).map (Rat.castHom ℝ)=lpsHeckeUpperGL ℝ p i := by sorry
