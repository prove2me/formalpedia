-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_sdg_geometric_convergence
-- name    : ShorNonsmooth.SpaceDilation.sdg_geometric_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:11:05.477053+00:00
-- url     : https://prove2.me/theorems/e5e93ff2-74e3-405b-b3cc-5a0d3d6cb6ab
-- title:
--   Theorem 3.4 — SDG function values converge at the geometric rate $\alpha^{-k/n}$
-- statement:
--   Let $f : E_n \to \mathbb{R}$ ($n \ge 1$), $x^* \in E_n$, $d > 0$, $S_d = \{x : \|x - x^*\| \le d\}$, and let $g : E_n \to E_n$ satisfy (3.18) on $S_d$,
--   $$
--   N\,[f(x) - f(x^*)] \le (g(x),\, x - x^*) \le M\,[f(x) - f(x^*)], \qquad M > N > 0 ,
--   $$
--   and let $G$ be a bound for $\|g\|$ on $S_d$ (the book's $G = \max_{x \in S_d}\|g_f(x)\|$). Run the SDG method with $B_0 = I$, $x_0 \in S_d$, stepsizes $h_{k+1} = \frac{2MN}{M+N}\,\frac{f(x_k) - f(x^*)}{\|\tilde g_k\|}$ and constant coefficient $1 < \alpha \le \frac{M+N}{M-N}$, as in Theorem 3.3. Then:
--
--   1. there exist a constant $c > 0$ and indices $k_1 < k_2 < \cdots$ with
--   $$
--   f(x_{k_p}) - f(x^*) \le c\,\alpha^{-k_p/n}, \qquad p = 1, 2, \dots;
--   $$
--   2. for every $k \ge 1$,
--   $$
--   \min_{0 \le i \le k-1}\,[f(x_i) - f(x^*)] \;\le\; \frac{G\sqrt{k(\alpha^2 - 1)}\;d}{N\sqrt{\alpha^{2k/n} - 1}} .
--   $$
--
--   The SDG method thus decreases function values at the speed of a geometric progression whose ratio $\alpha^{-1/n}$ depends only on the constants $M, N$ of (3.18) and on the dimension, and not on the conditioning of $f$ under nonsingular linear changes of variables.
--
--   **Formalization Note** The printed statement (p. 58) reads $\min_{1 \le i \le k}[f(x_i) - f(x^*)] \le G\sqrt{k(\alpha^2-1)}\,d/\sqrt{\alpha^{2k/n}-1}$. Its proof (p. 59) derives the bound with the factor $1/N$ from the lower inequality of (3.18), and the minimum comes from Theorem 3.2, whose proof bounds $\tilde g_0, \dots, \tilde g_{k-1}$; part 2 states what the proof establishes. The book takes $f$ almost differentiable and $g$ its almost-gradient; the Lean statement holds for every $g$ satisfying (3.18) and bounded by $G$ on $S_d$. The constant $c$ and the subsequence are chosen after all the data (they may depend on the run). $B_0 = I$ as in the proofs of Theorems 3.1–3.3. If the method stops at $g(x_k) = 0$, the state is repeated.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 58, Theorem 3.4 (proof p. 59)

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), pp. 58–59, Theorem 3.4, with the record bound its proof (p. 59) establishes.
Under the assumptions of Theorem 3.3 (with `B₀ = I`), and with `G` a bound for `‖g‖` on
`S_d = {x : ‖x - x*‖ ≤ d}` (the book's `G = max_{x ∈ S_d} ‖g_f(x)‖`):

1. there are a constant `c > 0` and a strictly increasing sequence of indices `k_p` with
   `f(x_{k_p}) - f(x*) ≤ c α^{-k_p/n}` for every `p`;
2. for every `k ≥ 1`, `min_{0 ≤ i ≤ k-1} [f(x_i) - f(x*)] ≤ G √(k(α² - 1)) d / (N √(α^{2k/n} - 1))`.

(The printed statement has no factor `1/N` and takes the minimum over `1 ≤ i ≤ k`; the proof
derives the bound with `1/N` from Theorem 3.2, whose proof bounds `g̃_0, …, g̃_{k-1}`.
See the mission's HARD.md.) -/
theorem sdg_geometric_convergence {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar x₀ : EuclideanSpace ℝ (Fin n)) (d M N α G : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hNM : N < M)
    (h318 : ∀ x ∈ Metric.closedBall xstar d,
      N * (f x - f xstar) ≤ inner ℝ (g x) (x - xstar) ∧
        inner ℝ (g x) (x - xstar) ≤ M * (f x - f xstar))
    (hG : ∀ x ∈ Metric.closedBall xstar d, ‖g x‖ ≤ G)
    (hx₀ : x₀ ∈ Metric.closedBall xstar d)
    (hα : 1 < α) (hαMN : α ≤ (M + N) / (M - N)) :
    (∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ,
        f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
            (ContinuousLinearEquiv.refl ℝ _) (kp p)).x - f xstar ≤
          c * α ^ (-(kp p : ℝ) / n)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ i : ℕ, i < k ∧
      f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
          (ContinuousLinearEquiv.refl ℝ _) i).x - f xstar ≤
        G * Real.sqrt (k * (α ^ 2 - 1)) * d / (N * Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1)) := by sorry

end ShorNonsmooth.SpaceDilation
