-- Prove2me | Theorems.Thm_SmoothJordanDomain_smoothJordanOutwardPoint_not_mem_closure
-- name    : SmoothJordanDomain.smoothJordanOutwardPoint_not_mem_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:19.126068+00:00
-- url     : https://prove2.me/theorems/ff850e76-dae4-59fd-aeb7-8aadbd2b56fb
-- title:
--   Smooth Jordan Domain: smooth Jordan Outward Point not mem closure
-- statement:
--   A boundary point pushed outward by the reciprocal of a strict radial
--   contraction lies outside the closed convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L52-L75
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L52-L75

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology

theorem SmoothJordanDomain.smoothJordanOutwardPoint_not_mem_closure
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanOutwardPoint c xi r ∉ closure Omega.carrier := by sorry
