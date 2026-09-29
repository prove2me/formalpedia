-- Prove2me | Theorems.Thm_TaoFivePrimes_downlow
-- name    : TaoFivePrimes.downlow
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T23:32:48.676985+00:00
-- url     : https://prove2.me/theorems/c03017c7-f4e7-4800-8aa3-f48b18a98f3d
-- title:
--   Tao Proposition 4.8: lower bound for the major-arc L^2 mass of S_{eta,q}
-- statement:
--   For a cutoff $\eta$, a modulus $q$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q)=1}\,\eta\!\left(\frac nx\right),$$
--
--   $\Lambda$ being the von Mangoldt function and $e(t)=e^{2\pi i t}$. Let $\eta$ be smooth, non-negative and supported in $[0,1]$, let $q\ge1$ and $x\ge1$, and let $0<r<\tfrac12$. Then
--
--   $$\int_{\|\alpha\|_{\mathbb R/\mathbb Z}\le r}\bigl|S_{\eta,q}(x,\alpha)\bigr|^{2}\,d\alpha
--   \;\ge\;\frac{\left(S_{\eta^{2},q}(x,0)-\dfrac{\|\eta''\|_{L^{1}(\mathbb R)}}{2\pi^{2}rx}\,S_{\eta,q}(x,0)\right)_{+}^{2}}
--   {\|\eta\|_{L^{2}(\mathbb R)}^{2}\,x+\|\eta\eta'\|_{L^{1}(\mathbb R)}},$$
--
--   where $\|\alpha\|_{\mathbb R/\mathbb Z}$ is the distance from $\alpha$ to the nearest integer, $S_{\eta^{2},q}$ is the same sum with the cutoff $\eta$ replaced by $\eta^{2}$, and $(u)_{+}=\max(0,u)$.
--
--   Discarding the error terms, the right-hand side is essentially $S_{\eta^{2},q}(x,0)$. The proposition therefore complements the upper bound of Corollary 4.7 and shows it to be sharp to within a factor of two whenever $rx$ is not too large; it is the source of the major-arc mass used in Corollary 4.9 and in Section 8.
--
--   **Fidelity note** The source states the numerator with $\|\eta'\eta'+\eta\eta''\|_{L^{1}}=\tfrac12\|(\eta^{2})''\|_{L^{1}}$ in place of $\tfrac12\|\eta''\|_{L^{1}}$. That is the constant one obtains by differentiating the cutoff $\eta^{2}$, whereas the auxiliary function appearing in the Parseval identity of the proof is built from $\eta$; the constant stated here is the one the argument produces.
--
--   **Formalization Note** The statement is given in cleared form, with the numerator squared on the left and the denominator multiplied out on the right, so no positivity of the denominator has to be assumed. Frequencies are real numbers: for $r\le\tfrac12$ the region $\|\alpha\|_{\mathbb R/\mathbb Z}\le r$ is the interval $[-r,r]$, and the integral over it agrees with the integral over $\mathbb R/\mathbb Z$ against the Haar probability measure.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Proposition 4.8

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory

theorem TaoFivePrimes.downlow
    (eta : ℝ → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) (hcs : HasCompactSupport eta)
    (hnn : ∀ t : ℝ, 0 ≤ eta t) (hsupp : ∀ t : ℝ, t < 0 ∨ 1 < t → eta t = 0)
    (q : ℕ) (x : ℝ) (hx : 1 ≤ x) (r : ℝ) (hr0 : 0 < r) (hr : r < 1 / 2) :
    (max 0 (‖TaoFivePrimes.smoothedExpSum (fun t => eta t ^ 2) q x 0‖
        - 1 / (2 * Real.pi ^ 2 * r * x) * (∫ t : ℝ, |iteratedDeriv 2 eta t|)
            * ‖TaoFivePrimes.smoothedExpSum eta q x 0‖)) ^ 2
      ≤ (x * (∫ t : ℝ, eta t ^ 2) + ∫ t : ℝ, |eta t * deriv eta t|)
          * ∫ theta in (-r)..r, ‖TaoFivePrimes.smoothedExpSum eta q x theta‖ ^ 2 := by sorry
