-- Prove2me | Theorems.Thm_SmoothJordanDomain_frontier_complexAffine
-- name    : SmoothJordanDomain.frontier_complexAffine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:46:28.722898+00:00
-- url     : https://prove2.me/theorems/a562ef46-8a90-4abd-8946-1af58211d5e6
-- title:
--   Smooth Jordan Domain: frontier complex Affine
-- statement:
--   The frontier of a complex-affine image is exactly the image of the
--   original frontier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L111-L118
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean#L111-L118

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real

theorem SmoothJordanDomain.frontier_complexAffine
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0) :
    frontier (Omega.complexAffine a b ha).carrier =
      (fun z => a * z + b) '' frontier Omega.carrier := by sorry
