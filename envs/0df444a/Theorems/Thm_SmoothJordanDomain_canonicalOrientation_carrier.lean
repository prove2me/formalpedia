-- Prove2me | Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
-- name    : SmoothJordanDomain.canonicalOrientation_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:04.668981+00:00
-- url     : https://prove2.me/theorems/ec48d76c-7ef5-53ed-b397-21fa93a5df7d
-- title:
--   Smooth Jordan Domain: canonical Orientation carrier
-- statement:
--   The Smooth Jordan Domain construction uses the canonical Orientation carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L368-L372
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean#L368-L372

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
set_option autoImplicit false
open Complex Set
open scoped Real

theorem SmoothJordanDomain.canonicalOrientation_carrier
    (Omega : SmoothJordanDomain) :
    Omega.canonicalOrientation.carrier = Omega.carrier := by sorry
