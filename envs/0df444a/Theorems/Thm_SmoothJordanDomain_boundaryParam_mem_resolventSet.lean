-- Prove2me | Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet
-- name    : SmoothJordanDomain.boundaryParam_mem_resolventSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:33:57.112124+00:00
-- url     : https://prove2.me/theorems/781a23fc-ee76-4682-a4bc-aef38f3682e5
-- title:
--   Smooth Jordan Domain: boundary Param mem resolvent Set
-- statement:
--   Every boundary point of a smooth Jordan domain that contains
--   `closure (numericalRange A)` belongs to the resolvent set of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L67-L78
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L67-L78

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
open SmoothJordanDomain

theorem SmoothJordanDomain.boundaryParam_mem_resolventSet [CompleteSpace E]
    (Omega : SmoothJordanDomain) (A : E →L[ℂ] E)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) (t : ℝ) :
    Omega.boundaryParam t ∈ resolventSet ℂ A := by sorry
