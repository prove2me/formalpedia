-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperMatrix_index_unique
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_index_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:15.815213+00:00
-- url     : https://prove2.me/theorems/d2ac4027-a837-4adb-9727-6601e9d7fb1c
-- title:
--   Tanner Lifted Product: lps Hecke Upper Matrix index unique
-- statement:
--   Integral factors cannot identify distinct standard representative indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L209-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeRepresentatives.lean#L209-L238

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsHeckeUpperMatrix_index_unique (p : ℕ) [Fact p.Prime]
    (i j : Option (Fin p)) (D : Matrix (Fin 2) (Fin 2) ℤ)
    (h : lpsHeckeUpperMatrix p i=D*lpsHeckeUpperMatrix p j) : i=j := by sorry
