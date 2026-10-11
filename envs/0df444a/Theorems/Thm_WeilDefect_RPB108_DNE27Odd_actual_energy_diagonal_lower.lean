-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_actual_energy_diagonal_lower
-- name    : WeilDefect.RPB108.DNE27Odd.actual_energy_diagonal_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:00:05.360988+00:00
-- url     : https://prove2.me/theorems/0c1fe591-bee8-4641-93a0-7252f2660408
-- title:
--   DNE27 odd — Actual retained energy gives a diagonal lower bound
-- statement:
--   Use the unchanged exact odd DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Let $z\in\mathbb C^4$, $U\in\mathbb R$, and $p,q\in\mathbb C$. Put $v(z)=R\sum_{i=1}^3|z_i|^2$, let $D$ be the native-dual square, $B$ the high mixed square, $N$ the low native coefficient, and $L_i$ the four exact lower weights. If $v(z)\le U$, $|p|^2\le DU$, and $|q|^2\le BU$, then
--
--   $$\sum_{i=0}^3L_i|z_i|^2\le N|z_0|^2-2|z_0||p-q|+U.$$
--
--   The actual energy is paid first. Its lower bound gives nonnegativity and subsequently supplies the retained coordinate term.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27ActualEnergy.lean#L80-L99; exact native theorem WeilDefect.RPB108.DNE27Odd.actual_energy_diagonal_lower. SHA256 f34d9946fe9000422ac90511b5df464891310b9591a7c05eed61c408d096ea5e. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
import Definitions.Def_RPB108_DNE27Gram_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.actual_energy_diagonal_lower (z : Fin 4 → ℂ) (Venergy : ℝ) (p q : ℂ)
    (hv : retainedEnergy z ≤ Venergy)
    (hp : ‖p‖^2 ≤ nativeDualSquare*Venergy)
    (hq : ‖q‖^2 ≤ highMixedSquare*Venergy) :
    (∑ i, lower i*‖z i‖^2) ≤
      nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+Venergy := by sorry
