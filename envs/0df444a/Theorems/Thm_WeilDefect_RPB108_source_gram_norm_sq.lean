-- Prove2me | Theorems.Thm_WeilDefect_RPB108_source_gram_norm_sq
-- name    : WeilDefect.RPB108.source_gram_norm_sq
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:27:31.910648+00:00
-- url     : https://prove2.me/theorems/17ec95c0-2999-491d-b3d1-8dbe14099d62
-- title:
--   Actual source norm from a real Gram realization
-- statement:
--   Let $E$ be a complex inner-product space and write $Q_G(w)=\sum_{i,j=0}^2G_{ij}\operatorname{Re}(\overline{w_i}w_j)$ for a real $3\times3$ matrix $G$. Let $r_i\in E$ for $i=0,1,2$ and assume $\langle r_i,r_j\rangle=G_{ij}$ as an equality in $\mathbb C$ for every pair. For every $z\in\mathbb C^3$,
--
--   $$\left\|\sum_i z_i r_i\right\|^2=Q_G(z).$$
--
--   This is an exact identity for actual vectors, with reality of all inner products explicitly assumed; no enumeration or abstract substitute is used.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SourcePairing.lean#L6-L22; exact native theorem WeilDefect.RPB108.source_gram_norm_sq. SHA256 ba90c8b11465f83dc965c1ed4c7657c17689a1ac3a9e74b76eb6f40f7f80bfaa. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.source_gram_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (r : Fin 3 → E) (G : Fin 3 → Fin 3 → ℝ)
    (hG : ∀ i j, inner ℂ (r i) (r j) = (G i j : ℂ)) (z : Fin 3 → ℂ) :
    ‖∑ i, z i • r i‖^2 = complexGram G z := by sorry
