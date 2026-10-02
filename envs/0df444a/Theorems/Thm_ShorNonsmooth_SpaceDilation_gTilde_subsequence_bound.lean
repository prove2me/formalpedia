-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_gTilde_subsequence_bound
-- name    : ShorNonsmooth.SpaceDilation.gTilde_subsequence_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:06:28.081039+00:00
-- url     : https://prove2.me/theorems/cf39c081-93f3-43f8-a035-37de913f6979
-- title:
--   Theorem 3.1 — along a subsequence $\|\tilde g_{k_p}\| < c\,(\prod_{j\le k_p}\alpha_j)^{-1/n}$
-- statement:
--   Run the SDG method in $E_n$ ($n \ge 1$) from a starting point $x_0$ with a nonsingular initial operator $B_0$, an arbitrary stepsize rule and space-dilation coefficients $\alpha_1, \alpha_2, \dots$; write $\tilde g_k = B_k^* g(x_k)$ for the transformed gradients. Suppose there are positive numbers $d$, $\alpha^*$, $\delta$ with
--
--   1. $\|g(x_k)\| \le d$ for $k = 0, 1, \dots$;
--   2. $1 + \delta \le \alpha_k \le \alpha^*$ for $k = 1, 2, \dots$.
--
--   Then there exist a constant $c > 0$ and indices $k_0 < k_1 < k_2 < \cdots$ such that
--   $$
--   \|\tilde g_{k_p}\| < c\,\Big(\prod_{j=1}^{k_p} \alpha_j\Big)^{-1/n}, \qquad p = 0, 1, \dots .
--   $$
--
--   Since $\prod_{j \le k} \alpha_j \ge (1+\delta)^k$, the transformed gradients become small at a geometric rate along a subsequence. This is the first step towards the convergence rate of function values in Theorem 3.4.
--
--   **Formalization Note** The book states the theorem for an almost differentiable $f$ with $g$ its almost-gradient; its proof uses only the bound $\|g(x_k)\| \le d$, so the Lean statement holds for every map $g$ and every stepsize rule, which is a generalization, not a weakening. The constant $c$ and the subsequence depend on the run and are chosen after all the data. If the method stops ($g(x_k) = 0$), the state is repeated and $\tilde g_k = 0$ from then on.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 53, Theorem 3.1

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), p. 53, Theorem 3.1. Let the SDG method be run with a nonsingular initial operator
`B₀`, any stepsize rule `h` and any generalized-gradient selection `g`. If for positive `d`, `α*`,
`δ` one has `‖g(x_k)‖ ≤ d` for `k = 0, 1, …` and `1 + δ ≤ α_k ≤ α*` for `k = 1, 2, …`, then there
are a constant `c > 0` and a strictly increasing sequence of indices `k_p` with
`‖g̃_{k_p}‖ < c (∏_{j=1}^{k_p} α_j)^{-1/n}` for every `p`.
(The book states it for an almost differentiable `f` with `g` an almost-gradient; the proof uses
only the bound `‖g(x_k)‖ ≤ d`, so the theorem is stated for every selection `g`.) -/
theorem gTilde_subsequence_bound {n : ℕ} (hn : 0 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) (α : ℕ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (B₀ : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d αstar δ : ℝ) (hd : 0 < d) (hαstar : 0 < αstar) (hδ : 0 < δ)
    (hg : ∀ k : ℕ, ‖g (sdg g h α x₀ B₀ k).x‖ ≤ d)
    (hα : ∀ k : ℕ, 1 ≤ k → 1 + δ ≤ α k ∧ α k ≤ αstar) :
    ∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ, ‖gTilde g h α x₀ B₀ (kp p)‖ <
        c * (∏ j ∈ Finset.Icc 1 (kp p), α j) ^ (-(1 : ℝ) / n) := by sorry

end ShorNonsmooth.SpaceDilation
