-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_native_pairing_square_of_enclosures
-- name    : WeilDefect.RPB108.DNE27Even.native_pairing_square_of_enclosures
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:25.470761+00:00
-- url     : https://prove2.me/theorems/fa1988d1-fd08-4e22-8ce1-1d3a575fbfef
-- title:
--   DNE27 even — Native pairing square from entry enclosures
-- statement:
--   For real $3\times3$ matrices, write $Q_V(w)=\sum_{i,j}V_{ij}\operatorname{Re}(\overline{w_i}w_j)$, and define $Q_G$ likewise. Use the unchanged exact even DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. Assume $\ell_i\le a_i\le u_i$ for all three row entries and all nine native matrix enclosures. Then for every $z\in\mathbb C^4$,
--
--   $$|P_a(z)|^2\le DQ_V(w).$$
--
--   The unsquared row intervals, exact dual budget and accepted retained-energy floor discharge the native pairing-square premise.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27NativePairing.lean#L50-L63; exact native theorem WeilDefect.RPB108.DNE27Even.native_pairing_square_of_enclosures. SHA256 281061491fd514610fe97f616372cb64afdb040ed1962333925ee71f3a06cc0f. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.native_pairing_square_of_enclosures (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 4 → ℂ) :
    ‖nativePairing a z‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ) := by sorry
