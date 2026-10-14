-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Even_strict_source_gram_domination
-- name    : WeilDefect.RPB108.DNE27Even.strict_source_gram_domination
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:58:56.993482+00:00
-- url     : https://prove2.me/theorems/661e3292-e90b-4283-8f0e-9d9f56048898
-- title:
--   DNE27 even — Strict scaled source/native Gram domination
-- statement:
--   For real matrices $A,V,G$ indexed by $\{0,1,2\}$ and complex coordinates $z$, write $Q_A(z)=\sum_{i,j}A_{ij}\operatorname{Re}(\overline{z_i}z_j)$, and for real coordinates $x$ write $R_A(x)=\sum_{i,j}A_{ij}x_ix_j$. For three off-diagonal bounds $u=(u_0,u_1,u_2)$, let $w_{01}=w_{10}=u_0$, $w_{02}=w_{20}=u_1$, $w_{12}=w_{21}=u_2$, and $w_{ii}=0$. Put $m(d,u)=(d_0-u_0-u_1,d_1-u_0-u_2,d_2-u_1-u_2)$. Use the unchanged exact even DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Assume the complete matrix enclosures and $z\in\mathbb C^3$ with $z\ne0$. Then
--
--   $$Q_G((s_i z_i)_i)<\rho Q_V((s_i z_i)_i).$$
--
--   Positive published margins make the difference strict. The exact scalar certificate $\rho<1$ is also checked as an embedded companion lemma; it is not an extra premise of this theorem.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27Gram.lean#L67-L79; exact native theorem WeilDefect.RPB108.DNE27Even.strict_source_gram_domination. SHA256 5a4a208bde5523e425bacd32d6077e0c32618162efd59bb6ab6628df50f1750a. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem WeilDefect.RPB108.DNE27Even.strict_source_gram_domination (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 3 → ℂ) (hz : z ≠ 0) :
    complexGram G (fun i => (gramScales i : ℂ)*z i) <
      rho*complexGram V (fun i => (gramScales i : ℂ)*z i) := by sorry
