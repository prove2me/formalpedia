-- Prove2me | Theorems.Thm_WeilDefect_RPB108_paid_actual_energy_lower
-- name    : WeilDefect.RPB108.paid_actual_energy_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:59:51.59819+00:00
-- url     : https://prove2.me/theorems/d2315a3e-7dd1-4094-8b5e-8eea248dd7bf
-- title:
--   Paid mixed row before retained-energy substitution
-- statement:
--   Let $A,M,\theta,x,V,v\in\mathbb R$ and $p,q\in\mathbb C$. Assume $0\le\theta<1$, $x,V\ge0$, $v\le V$, and $|p-q|\le M\sqrt V$. Then
--
--   $$(A-M^2/(1-\theta))x^2+\theta v\le Ax^2-2x|p-q|+V.$$
--
--   Complete the paid square against actual $V$ before introducing its lower bound $v$. No monotonicity of a negative square-root expression is needed.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/MixedPairing.lean#L34-L43; exact native theorem WeilDefect.RPB108.paid_actual_energy_lower. SHA256 a93c990b29d50c5536f57ca66d5750c92cbb38320e8b1188887c2cfdfbf85428. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.paid_actual_energy_lower (A M theta x V v : ℝ) (p q : ℂ)
    (ht0 : 0 ≤ theta) (ht1 : theta < 1) (hx : 0 ≤ x)
    (hV : 0 ≤ V) (hv : v ≤ V) (hpq : ‖p-q‖ ≤ M*Real.sqrt V) :
    (A-M^2/(1-theta))*x^2+theta*v ≤ A*x^2-2*x*‖p-q‖+V := by sorry
