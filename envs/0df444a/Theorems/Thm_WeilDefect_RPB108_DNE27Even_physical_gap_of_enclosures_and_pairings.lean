-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_enclosures_and_pairings
-- name    : WeilDefect.RPB108.DNE27Even.physical_gap_of_enclosures_and_pairings
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:00:27.154978+00:00
-- url     : https://prove2.me/theorems/560b568b-134d-4578-8af9-f03148619439
-- title:
--   DNE27 even — Physical gap with the retained-energy premise discharged
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. Use the unchanged exact even DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Let $E$ be a complex normed space, $T:E\to E$ a continuous complex-linear map, $x_i,\sigma_i\in E$ for $i=0,1,2,3$, $z\in\mathbb C^4$, $h\in E$, $e\in\mathbb R$, and $p,q\in\mathbb C$. Put $a=11/25$, $\delta=4/10^{36}$, $w_i=s_i z_{i+1}$ for $i=0,1,2$, $N$ for the low native coefficient, $D$ for the native-dual square, and $C$ for the raw low source square divided by $a^2$. Assume $\|T\|\le1/a$, $\|x_i\|\le n_i$, $\|\sigma_i\|^2\le b_i$ for the exact native-mass and source-square data, and the full matrix enclosures. Assume $|p|^2\le DQ_V(w)$, $|q|^2\le CQ_G(w)$, and the actual completion $N|z_0|^2-2|z_0||p-q|+Q_V(w)+a\|h\|^2\le e$. Under the specified norm, complete matrix-enclosure, pairing and actual-completion hypotheses,
--
--   $$\delta\left\|\sum_{i=0}^3 z_i(x_i-T\sigma_i)+h\right\|^2\le e.$$
--
--   The retained-energy premise is proved from the native intervals. Original-form operator, vector/source norm, matrix enclosure, pairing and completion attachments remain explicit and unproved for the original Weil form.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27RetainedEnergy.lean#L75-L95; exact native theorem WeilDefect.RPB108.DNE27Even.physical_gap_of_enclosures_and_pairings. SHA256 4a41ee4590c3cb7fb2d0ee15498dbafc45b1c6256b633b0d0bdb527587dd145b. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.physical_gap_of_enclosures_and_pairings {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ) (p q : ℂ)
    (hp : ‖p‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hq : ‖q‖^2 ≤ (rawSourceSquare 0/highFloor^2)*complexGram G
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hcompletion : nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by sorry
