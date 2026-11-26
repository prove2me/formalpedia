-- Prove2me | Theorems.Thm_SmoothJordanDomain_hasSmoothJordanOuterApproximation_closure
-- name    : SmoothJordanDomain.hasSmoothJordanOuterApproximation_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:19.844031+00:00
-- url     : https://prove2.me/theorems/3a7b26fc-56fb-5784-9f9b-b7e6e324f472
-- title:
--   Smooth Jordan Domain: has Smooth Jordan Outer Approximation closure
-- statement:
--   The closed carrier of a smooth Jordan domain admits arbitrarily tight
--   smooth Jordan outer approximations.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanInflation.lean#L18-L88
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanInflation.lean#L18-L88

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanInflation
set_option autoImplicit false
open Complex Metric Set

theorem SmoothJordanDomain.hasSmoothJordanOuterApproximation_closure
    (Omega : SmoothJordanDomain) :
    HasSmoothJordanOuterApproximation (closure Omega.carrier) := by sorry
