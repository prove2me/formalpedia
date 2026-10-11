-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_native_row_enclosures
-- name    : WeilDefect.RPB108.DNE27Odd.physical_gap_of_native_row_enclosures
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:28:02.097169+00:00
-- url     : https://prove2.me/theorems/8ca7869d-df54-4916-afe7-9d1996956c9a
-- title:
--   DNE27 odd — Physical gap with native pairing derived
-- statement:
--   For real $3\times3$ matrices, write $Q_V(w)=\sum_{i,j}V_{ij}\operatorname{Re}(\overline{w_i}w_j)$, and define $Q_G$ likewise. Use the unchanged exact odd DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. Put $k=11/25$ and $C=b_0^{\mathrm{raw}}/k^2$, with $b_0^{\mathrm{raw}}$ the exact raw low source-square datum. Let $E$ be a complex normed space (an inner-product space for the realized-source theorem), $T:E\to E$ continuous and complex-linear, $x_i,\sigma_i\in E$ for $i=0,1,2,3$, $z\in\mathbb C^4$, $h\in E$, and $e\in\mathbb R$. Assume $\|T\|\le1/k$, $\|x_i\|\le n_i$ and $\|\sigma_i\|^2\le b_i$ for the exact native mass and source-square data, both complete matrix enclosures, and $\ell_i\le a_i\le u_i$ for all native row entries. Write $N$ for the low native coefficient and $\delta=4/10^{36}$. Let $q\in\mathbb C$. In addition to the stated norm, matrix and row hypotheses, assume $|q|^2\le C Q_G(w)$ and $N|z_0|^2-2|z_0||P_a(z)-q|+Q_V(w)+k\|h\|^2\le e$. Then
--
--   $$\delta\left\|\sum_{i=0}^3z_i(x_i-T\sigma_i)+h\right\|^2\le e.$$
--
--   The native pairing and retained-energy estimates are derived. The source pairing-square premise and actual completion remain explicit.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27NativePairing.lean#L153-L175; exact native theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_native_row_enclosures. SHA256 281061491fd514610fe97f616372cb64afdb040ed1962333925ee71f3a06cc0f. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
import Definitions.Def_RPB108_DNE27NativePairing_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_native_row_enclosures {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ) (q : ℂ)
    (hq : ‖q‖^2 ≤ (rawSourceSquare 0/highFloor^2)*complexGram G
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hcompletion : nativeLow*‖z 0‖^2-2*‖z 0‖*‖nativePairing a z-q‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by sorry
