-- Prove2me | Theorems.Thm_ShorNonsmooth_RAlgorithm_pRatio_frequently_ge
-- name    : ShorNonsmooth.RAlgorithm.pRatio_frequently_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:14:40.800203+00:00
-- url     : https://prove2.me/theorems/68de7831-78e9-4eca-afcc-c1dbd47fb4d6
-- title:
--   Theorem 3.11 — along the $r(\alpha)$-algorithm, $p(\bar P_{\delta,\varepsilon}(x_k))$ is infinitely often at least $\sqrt{(v^2\alpha^{2/n}-1)/(\alpha^2-1)}$
-- statement:
--   Let $n \ge 1$, let $f \in K$ satisfy
--   $$
--   \lim_{\|x\| \to \infty} f(x) = +\infty \qquad (3.50),
--   $$
--   let $\alpha > 1$ and $\beta = 1/\alpha$, and let $\{x_k\}_{k=0}^\infty$ be a sequence constructed by the $r(\alpha)$-algorithm applied to $f$ (with any admissible choices of almost-gradients and stepsizes) such that
--   $$
--   \lim_{k \to \infty} \|x_{k+1} - x_k\| = 0 \qquad (3.52).
--   $$
--   Then for every fixed $v$ with $\sqrt[n]{\beta} < v < 1$, every $\varepsilon > 0$, $\delta > 0$ and every positive integer $r$ there exists $\bar k > r$ such that
--   $$
--   p\big(\bar P_{\delta,\varepsilon}(x_{\bar k})\big) \ge \sqrt{\frac{v^2 \sqrt[n]{\alpha^2} - 1}{\alpha^2 - 1}} .
--   $$
--
--   In words: infinitely often, the local set of almost-gradients around the iterate cannot be both thin and far from the origin. This is the quantitative core from which the convergence results of Section 3.7 are derived.
--
--   **Formalization Note** Condition (3.50) is the standing assumption of the section ("from now on we shall assume", p. 79) and the proof uses the boundedness of $\{x_k\}$ it implies, so it is a hypothesis here although the theorem's sentence does not repeat it. $p$ takes values in $[0, +\infty]$; the right-hand side is embedded with `ENNReal.ofReal`, and $\sqrt[n]{\cdot}$ is the real power $1/n$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 82, Theorem 3.11 (proof pp. 82–84); standing assumption (3.50), p. 79

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_RAlgorithm

open scoped InnerProductSpace ENNReal
open Filter Topology

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), p. 82, **Theorem 3.11**. Let `f ∈ K` (formed from the data `P`), satisfying the
standing condition (3.50) `f(x) → +∞` as `‖x‖ → ∞` (assumed "from now on", p. 79), let `α > 1`,
and let `{x_k}` be constructed by the `r(α)`-algorithm (the `r_μ(α)`-algorithm with `μ = 0`)
applied to `f`, with `lim_{k→∞} ‖x_{k+1} - x_k‖ = 0` (3.52). Then for each fixed `v` with
`ⁿ√β < v < 1` (`β = 1/α`), `ε > 0`, `δ > 0` and positive integer `r` there is `k̄ > r` with
`p(P̄_{δ,ε}(x_k̄)) ≥ √((v² ⁿ√(α²) - 1)/(α² - 1))`. -/
theorem pRatio_frequently_ge {n : ℕ} (hn : 0 < n) (P : KRep n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : P.Forms f)
    (hf_coercive : Tendsto f (cocompact (EuclideanSpace ℝ (Fin n))) atTop)
    (α : ℝ) (hα : 1 < α)
    (x gt g : ℕ → EuclideanSpace ℝ (Fin n))
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (hrun : IsRun P f α 0 x gt g B h)
    (hstep : Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0))
    (v : ℝ) (hv_gt : (1 / α) ^ (1 / (n : ℝ)) < v) (hv_lt : v < 1)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (r : ℕ) (hr : 0 < r) :
    ∃ kbar : ℕ, r < kbar ∧
      ENNReal.ofReal (Real.sqrt ((v ^ 2 * (α ^ 2) ^ (1 / (n : ℝ)) - 1) / (α ^ 2 - 1))) ≤
        pRatio (P.Pbar δ ε (x kbar)) := by sorry

end ShorNonsmooth.RAlgorithm
