-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:39.499281+00:00
-- url     : https://prove2.me/theorems/671aa83a-9ebc-428d-abaf-ca7dd168d337
-- title:
--   Tanner Lifted Product: lps Original JInvariant surjective
-- statement:
--   The SAME original j is surjective onto all complex values, proved by actual compact-connected constancy contradiction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L196-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L196-L211

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_surjective : Function.Surjective lpsOriginalJInvariant := by sorry
