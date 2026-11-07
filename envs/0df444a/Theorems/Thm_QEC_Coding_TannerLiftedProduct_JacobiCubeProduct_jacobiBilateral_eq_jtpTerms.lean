-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiBilateral_eq_jtpTerms
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiBilateral_eq_jtpTerms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:24:31.250868+00:00
-- url     : https://prove2.me/theorems/58879226-f53c-4d81-a831-a248f85000a6
-- title:
--   Jacobi Cube Product: jacobi Bilateral eq jtp Terms
-- statement:
--   The Jacobi Cube Product construction uses the jacobi Bilateral eq jtp Terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L547-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L547-L556

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.jacobiBilateral_eq_jtpTerms :
    jacobiBilateral =
      (∑' n : ℕ, jtpPositiveTerm n) + ∑' n : ℕ, jtpNegativeTerm n := by sorry
