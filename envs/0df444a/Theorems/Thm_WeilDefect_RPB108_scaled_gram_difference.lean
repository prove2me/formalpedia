-- Prove2me | Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
-- name    : WeilDefect.RPB108.scaled_gram_difference
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:59:37.281811+00:00
-- url     : https://prove2.me/theorems/04a4494b-8bac-4159-ad4f-980e7615eb02
-- title:
--   Exact column scaling of a Gram difference
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. For arbitrary real scales $s_i$, arbitrary real $\rho$, and every $z\in\mathbb C^3$,
--
--   $$Q_{(s_i s_j(\rho V_{ij}-G_{ij}))}(z)=\rho Q_V((s_i z_i)_i)-Q_G((s_i z_i)_i).$$
--
--   This is exact transform normalization, requiring no positivity hypothesis on the scales or matrices.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/ThreeGram.lean#L88-L101; exact native theorem WeilDefect.RPB108.scaled_gram_difference. SHA256 a442815ca3343f4cfad3b84e0834871dd329630111b0d35a9d569431a00eb5d8. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
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

theorem WeilDefect.RPB108.scaled_gram_difference (V G : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ)
    (rho : ℝ) (z : Fin 3 → ℂ) :
    complexGram (fun i j => s i*s j*(rho*V i j-G i j)) z =
      rho*complexGram V (fun i => (s i : ℂ)*z i)-
        complexGram G (fun i => (s i : ℂ)*z i) := by sorry
