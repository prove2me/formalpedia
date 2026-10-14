-- Prove2me | Theorems.Thm_WeilDefect_RPB108_complex_gram_lower
-- name    : WeilDefect.RPB108.complex_gram_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:58:53.507195+00:00
-- url     : https://prove2.me/theorems/9be36d2b-3119-4262-8489-18c581b84688
-- title:
--   Complex Gram bound from complete signed enclosures
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. Let $d,u\in\mathbb R^3$, $u_i\ge0$, $d_i\le A_{ii}$, and $|A_{ij}|\le w_{ij}$ for every distinct pair. For every $z\in\mathbb C^3$,
--
--   $$\sum_i m(d,u)_i|z_i|^2\le Q_A(z).$$
--
--   Apply the real bound to real and imaginary coordinates. No sampled-vector or matrix-symmetry premise is substituted for the complete enclosures.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/ThreeGram.lean#L50-L72; exact native theorem WeilDefect.RPB108.complex_gram_lower. SHA256 a442815ca3343f4cfad3b84e0834871dd329630111b0d35a9d569431a00eb5d8. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.complex_gram_lower (A : Fin 3 → Fin 3 → ℝ) (d u : Fin 3 → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, d i ≤ A i i)
    (ha : ∀ i j, i ≠ j → |A i j| ≤ offWeights u i j)
    (z : Fin 3 → ℂ) :
    (∑ i, rowMargins d u i*‖z i‖^2) ≤ complexGram A z := by sorry
