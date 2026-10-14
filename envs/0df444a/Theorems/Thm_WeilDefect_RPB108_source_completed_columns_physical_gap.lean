-- Prove2me | Theorems.Thm_WeilDefect_RPB108_source_completed_columns_physical_gap
-- name    : WeilDefect.RPB108.source_completed_columns_physical_gap
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T20:14:47.53327+00:00
-- url     : https://prove2.me/theorems/d3c33792-4300-4799-8f9e-36a685374b28
-- title:
--   Source completed columns physical gap
-- statement:
--   In every normed additive commutative group $E$ equipped with a complex normed vector-space structure, without a completeness assumption, let $T:E\to E$ be continuous and complex-linear, let $x_i,u_i\in E$ and $m_i,q_i,B_i,L_i\in\mathbb R$ for the four indices $i=0,1,2,3$, and let $k,g\in\mathbb R$. Assume $k>0$, $\|T\|\le1/k$, and, at every index, $\|x_i\|\le m_i$, $\|u_i\|^2\le q_i$, $m_i\le B_i$, $q_i\le\bigl(k(B_i-m_i)\bigr)^2$, and $L_i>0$. Also assume $g\ge0$ and $g\bigl(\sum_{i=0}^3B_i^2/L_i+1/k\bigr)\le1$. For every four complex coefficients $z_i$, vector $h\in E$, and real number $e$ satisfying $\sum_{i=0}^3L_i\|z_i\|^2+k\|h\|^2\le e$, the conclusion is $g\|\sum_{i=0}^3z_i(x_i-T(u_i))+h\|^2\le e$. The bounds imply $m_i,q_i,B_i,e\ge0$; zero gap, vectors, and coefficients are allowed. All sums have exactly four terms and all displayed denominators are precisely the strictly positive $L_i$ or $k$.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   monocap-tech/weil, post-Horizon-1 RPB108 conditional physical-gap library. Immutable native head ada7948cb459fd21d400cd8f2a92e87672e31f2d; SourceNormBounds.lean, line 59; SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84. All defining APIs are standard Mathlib; explicit original-form attachment hypotheses are retained.
--
--   Literature/source audit addendum (COR-23): This is an internally proved general algebra or norm estimate. Its exact graph type matches the native declaration WeilDefect.RPB108.source_completed_columns_physical_gap in WeilDefect/RPB108/SourceNormBounds.lean at ada7948cb459fd21d400cd8f2a92e87672e31f2d (SHA256 65422bd359b468153398bb574a6678bc54e47300e5ba0d96a398599c0ea69a84). Native bytes were verified against retained Git, and the library declarations were independently checked in Lean; public availability of the pin has not been checked. Any application to the original Weil form retains the supplied form/realization hypotheses. This record does not discharge original-form attachment, global continuation, or RH obligations.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem WeilDefect.RPB108.source_completed_columns_physical_gap {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (m q B L : Fin 4 → ℝ) (k gap : ℝ)
    (hk : 0 < k) (hT : ‖T‖ ≤ 1/k)
    (hx : ∀ i, ‖x i‖ ≤ m i) (hsource : ∀ i, ‖source i‖^2 ≤ q i)
    (hm : ∀ i, m i ≤ B i) (hq : ∀ i, q i ≤ (k*(B i-m i))^2)
    (hL : ∀ i, 0 < L i) (hgap : 0 ≤ gap)
    (hbound : gap * ((∑ i, (B i)^2/L i) + 1/k) ≤ 1)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (henergy : (∑ i, L i * ‖z i‖^2) + k*‖h‖^2 ≤ energy) :
    gap * ‖(∑ i, z i • (x i-T (source i))) + h‖^2 ≤ energy := by sorry
