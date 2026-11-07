-- Prove2me | Theorems.Thm_QubitFreqSensing_theorem_5_4
-- name    : QubitFreqSensing.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:21:58.19626+00:00
-- url     : https://prove2.me/theorems/6223994b-250e-4273-a23f-d13a44f2e0b6
-- title:
--   Theorem 5.4 — Rouché's theorem on the disc $\mathbb D_r$
-- statement:
--   Let $r>0$, and let $f,g$ be holomorphic on an open neighbourhood of the closed disc $\overline{\mathbb D_r}=\{|z|\le r\}$. If
--
--   $$
--   |g(z)|<|f(z)|\qquad\text{for all }|z|=r,
--   $$
--
--   then $f$ and $f+g$ have the same number of zeros, counted with multiplicity, in the open disc $\mathbb D_r=\{|z|<r\}$.
--
--   Rouché's theorem locates the zero of $z\mapsto\langle g_i,\Phi^{(i)}_zu\rangle$ inside $|z|<r/2$ in the proof of Lemma 5.9.
--
--   **Formalization Note** The number of zeros with multiplicity is $\sum_{z\in\mathbb D_r}\operatorname{ord}_z F$, a finite sum (`∑ᶠ` of `analyticOrderNatAt`).
--
--   Differences from the source:
--   - encoding: holomorphic on an open neighborhood of the closed disc; number of zeros counting multiplicity → AnalyticOnNhd ℂ on closedBall 0 r; ∑ᶠ z ∈ ball 0 r, analyticOrderNatAt; reason: Mathlib's notions; f and f + g are nonzero on the circle, so both counts are finite sums of finite orders
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Theorem 5.4, p.17 (PDF p.17)

import Mathlib

namespace QubitFreqSensing

/-- **Theorem 5.4** (Rouché's theorem; Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), Theorem 5.4, p.17). "Suppose f, g are two holomorphic functions on an open neighborhood
of the closed disc Dr, and suppose that |g(z)| < |f(z)| for all |z| = r. Then f and f + g have the
same number of zeros (counting multiplicity) on the open disc Dr."

**Formalization Note** "Holomorphic on an open neighborhood of the closed disc" is
`AnalyticOnNhd ℂ · (closedBall 0 r)`. The number of zeros counted with multiplicity on the open disc
`D_r = ball 0 r` is `∑ᶠ z ∈ ball 0 r, analyticOrderNatAt F z` (the order of vanishing of `F` at `z`,
`0` where `F z ≠ 0`); under the hypotheses neither `f` nor `f + g` vanishes on the circle or
identically, so both sums are finite sums of finite orders. -/
theorem theorem_5_4 (f g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 r))
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 r))
    (hlt : ∀ z : ℂ, ‖z‖ = r → ‖g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ Metric.ball (0 : ℂ) r, analyticOrderNatAt f z) =
      ∑ᶠ z ∈ Metric.ball (0 : ℂ) r, analyticOrderNatAt (f + g) z := by sorry

end QubitFreqSensing
