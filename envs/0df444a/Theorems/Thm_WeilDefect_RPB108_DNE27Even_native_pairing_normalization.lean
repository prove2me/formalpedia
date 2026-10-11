-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_native_pairing_normalization
-- name    : WeilDefect.RPB108.DNE27Even.native_pairing_normalization
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:18.883676+00:00
-- url     : https://prove2.me/theorems/52e45aa7-4e09-4e6c-addc-7e246526faa5
-- title:
--   DNE27 even — Exact native row and column-scale normalization
-- statement:
--   For real $3\times3$ matrices, write $Q_V(w)=\sum_{i,j}V_{ij}\operatorname{Re}(\overline{w_i}w_j)$, and define $Q_G$ likewise. Use the unchanged exact even DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. For every real row $a$ and every $z\in\mathbb C^4$,
--
--   $$P_a(z)=\sum_i a_i(s_i z_{i+1}).$$
--
--   Column scaling is transported exactly, with unchanged complex coercions and retained coordinate order.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27NativePairing.lean#L18-L25; exact native theorem WeilDefect.RPB108.DNE27Even.native_pairing_normalization. SHA256 281061491fd514610fe97f616372cb64afdb040ed1962333925ee71f3a06cc0f. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.native_pairing_normalization (a : Fin 3 → ℝ) (z : Fin 4 → ℂ) :
    nativePairing a z = ∑ i : Fin 3, (a i : ℂ)*((gramScales i : ℂ)*z i.succ) := by sorry
