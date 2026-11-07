-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_jtpIntegerTerm_jacobiBilateral
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_jtpIntegerTerm_jacobiBilateral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:42.806046+00:00
-- url     : https://prove2.me/theorems/4cb08515-1b6f-4704-a094-07a10861bcd6
-- title:
--   Jacobi Cube Product: has Sum jtp Integer Term jacobi Bilateral
-- statement:
--   The split definition of `jacobiBilateral` is the sum of the uniform
--   integer-indexed family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L560-L578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L560-L578

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_jtpIntegerTerm_jacobiBilateral :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum jtpIntegerTerm jacobiBilateral := by sorry
