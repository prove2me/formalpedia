-- Prove2me | Theorems.Thm_SmoothJordanDomain_isCompact_frontier
-- name    : SmoothJordanDomain.isCompact_frontier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:48:40.627247+00:00
-- url     : https://prove2.me/theorems/2ab72dff-3737-4e74-a3d6-9f1fa1062431
-- title:
--   Smooth Jordan Domain: is Compact frontier
-- statement:
--   The frontier of a smooth Jordan domain is compact: it is the range of a
--   continuous function with nonzero period.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L61-L65
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/GeneralSymmetrized.lean#L61-L65

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_SymmetrizedAuxiliary
import Definitions.Def_Operator_Crouzeix_SymmetrizedBound
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
open SmoothJordanDomain

theorem SmoothJordanDomain.isCompact_frontier (Omega : SmoothJordanDomain) :
    IsCompact (frontier Omega.carrier) := by sorry
