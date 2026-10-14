-- Prove2me | Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_gram_and_pairings
-- name    : WeilDefect.RPB108.DNE27Odd.physical_gap_of_gram_and_pairings
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T03:59:18.578503+00:00
-- url     : https://prove2.me/theorems/1c2ba11c-951a-4de1-95fb-72ab0d6ef0ad
-- title:
--   DNE27 odd — Physical gap from Gram and actual-energy attachments
-- statement:
--   Use the unchanged exact odd DNE27 rational data. Let $s_i$ denote the three retained column scales, $\rho$ the source/native Gram ratio, $d_i$ the scaled-difference diagonal lower entries, $u_i$ its off-diagonal bounds, and $\mu_i$ the published positive row margins. Let $R$ be the retained lower coefficient and $\theta$ the paid Young parameter. Write $V^-\le V\le V^+$ and $G^-\le G\le G^+$ for all nine entrywise lower/upper enclosure hypotheses, with no silent symmetry assumption. Let $E$ be a complex normed space, $T:E\to E$ a continuous complex-linear map, $x_i,\sigma_i\in E$ for $i=0,1,2,3$, $z\in\mathbb C^4$, $h\in E$, $e\in\mathbb R$, and $p,q\in\mathbb C$. Put $a=11/25$, $\delta=4/10^{36}$, $w_i=s_i z_{i+1}$ for $i=0,1,2$, $N$ for the low native coefficient, $D$ for the native-dual square, and $C$ for the raw low source square divided by $a^2$. Assume $\|T\|\le1/a$, $\|x_i\|\le n_i$, $\|\sigma_i\|^2\le b_i$ for the exact native-mass and source-square data, and the full matrix enclosures. Assume $|p|^2\le DQ_V(w)$, $|q|^2\le CQ_G(w)$, and the actual completion $N|z_0|^2-2|z_0||p-q|+Q_V(w)+a\|h\|^2\le e$. In addition to the specified norm, matrix, pairing and completion hypotheses, assume $R\sum_{i=1}^3|z_i|^2\le Q_V(w)$. Then
--
--   $$\delta\left\|\sum_{i=0}^3 z_i(x_i-T\sigma_i)+h\right\|^2\le e.$$
--
--   This conditional theorem retains the actual retained-energy premise as well as all original-form norm, operator, pairing and completion attachments.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27ActualEnergy.lean#L101-L141; exact native theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_gram_and_pairings. SHA256 f34d9946fe9000422ac90511b5df464891310b9591a7c05eed61c408d096ea5e. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem WeilDefect.RPB108.DNE27Odd.physical_gap_of_gram_and_pairings {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ) (p q : ℂ)
    (hv : retainedEnergy z ≤ complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hp : ‖p‖^2 ≤ nativeDualSquare*complexGram V
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hq : ‖q‖^2 ≤ (rawSourceSquare 0/highFloor^2)*complexGram G
      (fun i => (gramScales i : ℂ)*z i.succ))
    (hcompletion : nativeLow*‖z 0‖^2-2*‖z 0‖*‖p-q‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by sorry
