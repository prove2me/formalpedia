-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_signedEuler_jtpPairs
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:44.940427+00:00
-- url     : https://prove2.me/theorems/00317ba1-1d2a-4c55-9ace-bbe71dfaf1e6
-- title:
--   Jacobi Cube Product: has Sum signed Euler jtp Pairs
-- statement:
--   The Jacobi Cube Product construction uses the has Sum signed Euler jtp Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L707-L747
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L707-L747

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpPairs :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun t : ℕ =>
        signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
          signedEuler (jtpIntegerTerm (-(t : ℤ))))
      (signedEuler jacobiBilateral) := by sorry
