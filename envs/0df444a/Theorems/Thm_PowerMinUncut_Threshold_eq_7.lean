-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_eq_7
-- name    : PowerMinUncut.Threshold.eq_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:45:08.146704+00:00
-- url     : https://prove2.me/theorems/3f67c91d-ba40-4646-a99c-1ee9c7930d2f
-- title:
--   §4.2, Eq. (7) — fixed-sphere nonlocal endpoint: liminf_{θ↓0} inf_F E_θ(F)/θ^q ≥ C_{k,q} b(d,q)/a(d,q)
-- statement:
--   Let $q\ge2$ and $k>q$ be integers (§4 assumes $k>q$), and $d\ge\max\{2,k-1\}$. For $\theta>0$ and a measurable $F:S^d\to S^{k-1}$ let $E_\theta(F)=\mathbb E\|F(x)+F(-z)\|^q$, $x$ uniform on $S^d$ and $z$ uniform on $\{\langle x,z\rangle=\cos\theta\}$. Then
--   $$\liminf_{\theta\downarrow0}\ \inf_{F:S^d\to S^{k-1}}\frac{E_\theta(F)}{\theta^q}\ \ge\ C_{k,q}\,\frac{b(d,q)}{a(d,q)}.\tag{7}$$
--   The maps are merely measurable and need not be odd. Letting $d\to\infty$ ($b/a\to1$) gives the lower bound of Theorem 3.
--
--   Differences from the source:
--   - encoding: liminf_{θ↓0} g(θ) ≥ L → for every ε > 0, eventually as θ → 0⁺, g(θ) ≥ L − ε; reason: equivalent formulation of the lower limit without extended reals
--   - encoding: x uniform on S^d, z uniform on {⟨x, z⟩ = cos θ} → x = X/‖X‖, z = cos θ·x + sin θ·u with u the normalized component of Y ⊥ x, X, Y independent Gaussians; reason: this pair has the rotation-invariant angle-θ law
--   - encoding: measurable F : S^d → S^{k−1} → measurable F : ℝ^{d+1} → ℝ^k with ‖F(x)‖ = 1 for x ∈ S^d; reason: E_θ reads F only on S^d (almost surely), and every measurable map on S^d extends measurably to ℝ^{d+1}, so the infimum is the same
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 10, §4.1 and p. 11, §4.2, Eq. (7)

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Instance
import Definitions.Def_PowerMinUncut_Threshold_Sobolev

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **§4.2, Eq. (7)**, p. 11. For integers `q ≥ 2`, `k > q` and `d ≥ max{2, k - 1}`:
`liminf_{θ↓0} inf_{F : S^d → S^{k-1}} E_θ(F)/θ^q ≥ C_{k,q} b(d,q)/a(d,q)`, the infimum over
measurable maps (stated as: for every `ε > 0`, eventually as `θ ↓ 0` the infimum is at least
`C_{k,q} b(d,q)/a(d,q) - ε`). -/
theorem eq_7 (q k d : ℕ) (hq : 2 ≤ q) (hkq : q < k) (hd : 2 ≤ d) (hdk : k - 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      Ckp k q * bFun (d : ℝ) q / aFun (d : ℝ) q - ε ≤ shellInf d k q θ := by sorry

end PowerMinUncut.Threshold
