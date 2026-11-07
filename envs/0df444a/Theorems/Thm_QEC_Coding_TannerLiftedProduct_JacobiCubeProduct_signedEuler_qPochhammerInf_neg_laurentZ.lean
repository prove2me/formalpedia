-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_qPochhammerInf_neg_laurentZ
-- name    : QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_qPochhammerInf_neg_laurentZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:23:29.10919+00:00
-- url     : https://prove2.me/theorems/16a66229-4eb6-45de-8a46-15c1199dc292
-- title:
--   Jacobi Cube Product: signed Euler q Pochhammer Inf neg laurent Z
-- statement:
--   The Jacobi Cube Product construction uses the signed Euler q Pochhammer Inf neg laurent Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L231-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeProduct.lean#L231-L252

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

theorem QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_qPochhammerInf_neg_laurentZ :
    signedEuler (qPochhammerInf (-laurentZ)) =
      -eulerProduct := by sorry
