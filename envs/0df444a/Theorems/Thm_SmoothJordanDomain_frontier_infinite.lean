-- Prove2me | Theorems.Thm_SmoothJordanDomain_frontier_infinite
-- name    : SmoothJordanDomain.frontier_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:38.261347+00:00
-- url     : https://prove2.me/theorems/2b3f769a-6051-4c87-96f5-d28f711d4208
-- title:
--   Smooth Jordan Domain: frontier infinite
-- statement:
--   Every smooth Jordan frontier is infinite.  The boundary parametrization
--   is injective on the infinite half-open fundamental interval, whose image lies
--   in its full range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L49-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L49-L55

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem SmoothJordanDomain.frontier_infinite (Omega : SmoothJordanDomain) :
    (frontier Omega.carrier).Infinite := by sorry
