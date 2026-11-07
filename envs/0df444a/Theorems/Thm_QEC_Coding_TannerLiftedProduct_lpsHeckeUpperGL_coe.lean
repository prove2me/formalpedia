-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:42.96386+00:00
-- url     : https://prove2.me/theorems/2e5d0635-1408-4a4b-941d-16a26617e13e
-- title:
--   Tanner Lifted Product: lps Hecke Upper GL coe
-- statement:
--   The GL matrix has exactly the integral representative entries after casting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L315-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L315-L318

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_coe (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i : Matrix (Fin 2) (Fin 2) R)=
      (lpsHeckeUpperMatrix p i).map (Int.castRingHom R) := by sorry
