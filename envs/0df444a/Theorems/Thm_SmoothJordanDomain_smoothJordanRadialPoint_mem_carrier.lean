-- Prove2me | Theorems.Thm_SmoothJordanDomain_smoothJordanRadialPoint_mem_carrier
-- name    : SmoothJordanDomain.smoothJordanRadialPoint_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:33.944058+00:00
-- url     : https://prove2.me/theorems/73d1be28-c8e6-40c4-87b7-e635d2490ccd
-- title:
--   Smooth Jordan Domain: smooth Jordan Radial Point mem carrier
-- statement:
--   Strict radial contractions of points in the closed carrier lie in its
--   open interior.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L79-L91
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyan.lean#L79-L91

import Definitions.Def_Operator_Crouzeix_ConvexRungeIntegral
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
set_option autoImplicit false
open Complex Filter Metric Set
open scoped Interval Real Topology

theorem SmoothJordanDomain.smoothJordanRadialPoint_mem_carrier
    (Omega : SmoothJordanDomain) {c z : ℂ}
    (hc : c ∈ Omega.carrier) (hz : z ∈ closure Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    smoothJordanRadialPoint c z r ∈ Omega.carrier := by sorry
