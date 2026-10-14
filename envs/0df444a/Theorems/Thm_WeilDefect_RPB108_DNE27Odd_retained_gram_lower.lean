-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_retained_gram_lower
-- name    : WeilDefect.RPB108.DNE27Odd.retained_gram_lower
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:58:55.702866+00:00
-- url     : https://prove2.me/theorems/58a15685-af71-4db5-951e-b849893da3f2
-- title:
--   DNE27 odd — Retained energy floor from complete native intervals
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. Use the unchanged exact odd DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Assume $V^-\le V\le V^+$ entrywise for all nine entries. For every $z\in\mathbb C^3$,
--
--   $$R\sum_i|z_i|^2\le Q_V((s_i z_i)_i).$$
--
--   The native intervals alone give the retained floor after exact column congruence; no source matrix or pairing premise is required.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27RetainedEnergy.lean#L126-L154; exact native theorem WeilDefect.RPB108.DNE27Odd.retained_gram_lower. SHA256 4a41ee4590c3cb7fb2d0ee15498dbafc45b1c6256b633b0d0bdb527587dd145b. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27RetainedEnergy_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.retained_gram_lower (V : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (z : Fin 3 → ℂ) :
    retainedLower*(∑ i, ‖z i‖^2) ≤
      complexGram V (fun i => (gramScales i : ℂ)*z i) := by sorry
