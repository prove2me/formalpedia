-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_inverse_source_pairing_square_of_gram
-- name    : WeilDefect.RPB108.DNE27Even.inverse_source_pairing_square_of_gram
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:42.303622+00:00
-- url     : https://prove2.me/theorems/f2abe19c-cc85-40b7-ade4-40a2f981c6b9
-- title:
--   DNE27 even — Inverse-source pairing square from actual Gram data
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Use the unchanged exact even DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. For four actual source vectors $\sigma_0,\ldots,\sigma_3\in E$ and a continuous complex-linear map $T:E\to E$, define $J_T(\sigma,z)=\langle\sigma_0,T(\sum_i z_{i+1}\sigma_{i+1})\rangle$. The source realization hypothesis is $\langle\sigma_{i+1},\sigma_{j+1}\rangle=s_i s_jG_{ij}$ for every pair; in particular every one of these inner products is real. Let $k=11/25$ and $C=b_0^{\mathrm{raw}}/k^2$, where $b_0^{\mathrm{raw}}$ is the exact raw low source-square datum. Assume $\|T\|\le1/k$, $\|\sigma_0\|^2\le b_0$, and the full source realization hypothesis. For every $z\in\mathbb C^4$,
--
--   $$|J_T(\sigma,z)|^2\le C Q_G(w).$$
--
--   The exact low-scale identity, actual retained source norm and Cauchy/operator estimate derive the source pairing-square bound. The same supplied map T is used throughout.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SourcePairing.lean#L29-L44; exact native theorem WeilDefect.RPB108.DNE27Even.inverse_source_pairing_square_of_gram. SHA256 498d343d111ed242d24172da2d719cf493eb78251dc2d20676f79374bbe10800. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SourcePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.inverse_source_pairing_square_of_gram {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (source : Fin 4 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hT : ‖T‖ ≤ 1/highFloor) (hsource0 : ‖source 0‖^2 ≤ sourceSquare 0)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    ‖inverseSourcePairing T source z‖^2 ≤ (rawSourceSquare 0/highFloor^2)*
      complexGram G (fun i => (gramScales i : ℂ)*z i.succ) := by sorry
