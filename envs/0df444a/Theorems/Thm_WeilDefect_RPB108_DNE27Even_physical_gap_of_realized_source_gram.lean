-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_realized_source_gram
-- name    : WeilDefect.RPB108.DNE27Even.physical_gap_of_realized_source_gram
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:56.331329+00:00
-- url     : https://prove2.me/theorems/e3b6274e-1239-4002-aaa3-789bdd4d8fd2
-- title:
--   DNE27 even — Physical gap with both pairing estimates derived
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Use the unchanged exact even DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. For four actual source vectors $\sigma_0,\ldots,\sigma_3\in E$ and a continuous complex-linear map $T:E\to E$, define $J_T(\sigma,z)=\langle\sigma_0,T(\sum_i z_{i+1}\sigma_{i+1})\rangle$. The source realization hypothesis is $\langle\sigma_{i+1},\sigma_{j+1}\rangle=s_i s_jG_{ij}$ for every pair; in particular every one of these inner products is real. Let $k=11/25$ and $C=b_0^{\mathrm{raw}}/k^2$, where $b_0^{\mathrm{raw}}$ is the exact raw low source-square datum. Let $E$ be a complex normed space (an inner-product space for the realized-source theorem), $T:E\to E$ continuous and complex-linear, $x_i,\sigma_i\in E$ for $i=0,1,2,3$, $z\in\mathbb C^4$, $h\in E$, and $e\in\mathbb R$. Assume $\|T\|\le1/k$, $\|x_i\|\le n_i$ and $\|\sigma_i\|^2\le b_i$ for the exact native mass and source-square data, both complete matrix enclosures, and $\ell_i\le a_i\le u_i$ for all native row entries. Write $N$ for the low native coefficient and $\delta=4/10^{36}$. Assume also the full source realization hypothesis and $N|z_0|^2-2|z_0||P_a(z)-J_T(\sigma,z)|+Q_V(w)+k\|h\|^2\le e$. Then
--
--   $$\delta\left\|\sum_{i=0}^3z_i(x_i-T\sigma_i)+h\right\|^2\le e.$$
--
--   Both mixed pairing-square estimates are proved from row enclosures and the actual source Gram identity. Operator, vector norm, matrix/row enclosures, Gram realization and completion attachments for the original Weil form remain unproved caller obligations.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SourcePairing.lean#L46-L69; exact native theorem WeilDefect.RPB108.DNE27Even.physical_gap_of_realized_source_gram. SHA256 498d343d111ed242d24172da2d719cf493eb78251dc2d20676f79374bbe10800. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
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

theorem WeilDefect.RPB108.DNE27Even.physical_gap_of_realized_source_gram {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ))
    (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (hcompletion : nativeLow*‖z 0‖^2-
      2*‖z 0‖*‖nativePairing a z-inverseSourcePairing T source z‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by sorry
