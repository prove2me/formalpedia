-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_retained_source_norm_sq
-- name    : WeilDefect.RPB108.DNE27Even.retained_source_norm_sq
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:28:14.451573+00:00
-- url     : https://prove2.me/theorems/89c3ad56-87b3-4e14-b967-f309926fe46a
-- title:
--   DNE27 even — Exact norm of the realized retained source combination
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Use the unchanged exact even DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. For four actual source vectors $\sigma_0,\ldots,\sigma_3\in E$ and a continuous complex-linear map $T:E\to E$, define $J_T(\sigma,z)=\langle\sigma_0,T(\sum_i z_{i+1}\sigma_{i+1})\rangle$. The source realization hypothesis is $\langle\sigma_{i+1},\sigma_{j+1}\rangle=s_i s_jG_{ij}$ for every pair; in particular every one of these inner products is real. Let $k=11/25$ and $C=b_0^{\mathrm{raw}}/k^2$, where $b_0^{\mathrm{raw}}$ is the exact raw low source-square datum. Under the full source realization hypothesis, for every $z\in\mathbb C^4$,
--
--   $$\left\|\sum_i z_{i+1}\sigma_{i+1}\right\|^2=Q_G(w).$$
--
--   The existing four-column frame and all scale factors are preserved. This identifies a raw source norm, not an inverse covariance.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SourcePairing.lean#L13-L22; exact native theorem WeilDefect.RPB108.DNE27Even.retained_source_norm_sq. SHA256 498d343d111ed242d24172da2d719cf493eb78251dc2d20676f79374bbe10800. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27SourcePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.retained_source_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (source : Fin 4 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    ‖∑ i : Fin 3, z i.succ • source i.succ‖^2 =
      complexGram G (fun i => (gramScales i : ℂ)*z i.succ) := by sorry
