-- Prove2me | Theorems.Thm_WeilDefect_RPB108_inverse_source_pairing_square
-- name    : WeilDefect.RPB108.inverse_source_pairing_square
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:26:40.815349+00:00
-- url     : https://prove2.me/theorems/c3a9685a-f8da-4539-9bc5-ddaa69bcd017
-- title:
--   Actual source pairing bound from an operator norm
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Let $r,v\in E$, $T:E\to E$ continuous and complex-linear, and $P,k\in\mathbb R$. Assume $k>0$, $\|T\|\le1/k$, and $\|r\|^2\le P$. Then
--
--   $$|\langle r,Tv\rangle|^2\le(P/k^2)\|v\|^2.$$
--
--   Cauchy and the supplied operator bound prove the estimate. No inverse equation or raw-Gram/inverse-covariance identity is assumed implicitly.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SourcePairing.lean#L24-L41; exact native theorem WeilDefect.RPB108.inverse_source_pairing_square. SHA256 ba90c8b11465f83dc965c1ed4c7657c17689a1ac3a9e74b76eb6f40f7f80bfaa. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.inverse_source_pairing_square {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r v : E) (P k : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k) (hr : ‖r‖^2 ≤ P) :
    ‖inner ℂ r (T v)‖^2 ≤ (P/k^2)*‖v‖^2 := by sorry
