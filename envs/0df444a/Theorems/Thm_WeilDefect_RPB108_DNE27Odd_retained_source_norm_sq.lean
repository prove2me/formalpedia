-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_source_norm_sq
-- name    : WeilDefect.RPB108.DNE27Odd.retained_source_norm_sq
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:07.163658+00:00
-- url     : https://prove2.me/theorems/fbf763a5-a97a-4d8a-9f7b-55ab55cf6d92
-- title:
--   DNE27 odd — Exact norm of the realized retained source combination
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Use the unchanged exact odd DNE27 rational data. Indices $i,j$ range over $0,1,2$. Let $s_i$ be the retained column scales, $D$ the native-dual square, $R$ the retained lower coefficient, $\ell_i,u_i$ the native row lower and upper entries, and $a_i$ supplied real row entries. For $z\in\mathbb C^4$, put $w_i=s_i z_{i+1}$ and $P_a(z)=\sum_i(s_i a_i)z_{i+1}$. All native matrix enclosures mean the nine entrywise inequalities $V^-_{ij}\le V_{ij}\le V^+_{ij}$; source enclosures mean $G^-_{ij}\le G_{ij}\le G^+_{ij}$. For four actual source vectors $\sigma_0,\ldots,\sigma_3\in E$ and a continuous complex-linear map $T:E\to E$, define $J_T(\sigma,z)=\langle\sigma_0,T(\sum_i z_{i+1}\sigma_{i+1})\rangle$. The source realization hypothesis is $\langle\sigma_{i+1},\sigma_{j+1}\rangle=s_i s_jG_{ij}$ for every pair; in particular every one of these inner products is real. Let $k=11/25$ and $C=b_0^{\mathrm{raw}}/k^2$, where $b_0^{\mathrm{raw}}$ is the exact raw low source-square datum. Under the full source realization hypothesis, for every $z\in\mathbb C^4$,
--
--   $$\left\|\sum_i z_{i+1}\sigma_{i+1}\right\|^2=Q_G(w).$$
--
--   The existing four-column frame and all scale factors are preserved. This identifies a raw source norm, not an inverse covariance.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SourcePairing.lean#L83-L92; exact native theorem WeilDefect.RPB108.DNE27Odd.retained_source_norm_sq. SHA256 498d343d111ed242d24172da2d719cf493eb78251dc2d20676f79374bbe10800. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27SourcePairing_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.retained_source_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (source : Fin 4 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ)) (z : Fin 4 → ℂ) :
    ‖∑ i : Fin 3, z i.succ • source i.succ‖^2 =
      complexGram G (fun i => (gramScales i : ℂ)*z i.succ) := by sorry
