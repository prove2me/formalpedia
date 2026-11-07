-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_jacobiTripleProduct
-- name    : QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.jacobiTripleProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:53:58.842573+00:00
-- url     : https://prove2.me/theorems/1f01255f-a6d7-4942-a7d7-8d233283f2fd
-- title:
--   Formal Power Series: jacobi Triple Product
-- statement:
--   jacobiProd = jacobiBilateral via HasSum.mul, diagonalEquiv, and diagonal HasSum results.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L710-L712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/FPSAlgebra.lean#L710-L712

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSEuler
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FiniteBinomial
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
set_option autoImplicit false
noncomputable section
open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiGeneralCore QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
open LaurentPolynomial

theorem QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.jacobiTripleProduct : @jacobiProd = @jacobiBilateral := by sorry
