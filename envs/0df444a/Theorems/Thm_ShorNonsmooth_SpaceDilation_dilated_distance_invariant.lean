-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilated_distance_invariant
-- name    : ShorNonsmooth.SpaceDilation.dilated_distance_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:07:36.277973+00:00
-- url     : https://prove2.me/theorems/bbf3deb6-44b6-4433-b347-574e6da21222
-- title:
--   Theorem 3.3 — the SDG iterates satisfy $\|A_k(x_k - x^*)\| \le d$
-- statement:
--   Let $f : E_n \to \mathbb{R}$, let $x^* \in E_n$ and $d > 0$, and let $S_d = \{x : \|x - x^*\| \le d\}$. Let $g : E_n \to E_n$ satisfy, for every $x \in S_d$,
--   $$
--   N\,[f(x) - f(x^*)] \;\le\; (g(x),\, x - x^*) \;\le\; M\,[f(x) - f(x^*)], \qquad (3.18)
--   $$
--   where $M > N > 0$. Run the SDG method with $B_0 = I$ and
--
--   1. $x_0 \in S_d$;
--   2. $h_{k+1} = \dfrac{2MN}{M+N}\,\dfrac{f(x_k) - f(x^*)}{\|\tilde g_k\|}$, $\quad$ (3.19)
--   3. $1 < \alpha_{k+1} = \alpha \le \dfrac{M+N}{M-N}$, $\quad k = 0, 1, 2, \dots$ $\quad$ (3.20)
--
--   Then
--   $$
--   \|A_k(x_k - x^*)\| \le d \qquad \text{for } k = 0, 1, 2, \dots .
--   $$
--
--   The distance from the iterate to $x^*$, measured in the transformed space, never exceeds its initial value; in particular all iterates stay in $S_d$. This invariant is what lets Theorems 3.1 and 3.2 be applied to function values in Theorem 3.4.
--
--   **Formalization Note** The book takes $f$ almost differentiable on $S_d$, $g$ its almost-gradient and $x^*$ a local minimum point; the proof uses only (3.18), so the Lean statement holds for every $f$ on $E_n$ and every $g$ satisfying (3.18) on $S_d$ (a generalization). Condition (3.18) with $M > N > 0$ already forces $f(x) \ge f(x^*)$ on $S_d$. The proof's $A_0 = I$ is assumed ($B_0 = I$); for another $B_0$ the claim fails at $k = 0$. The stepsize (3.19) is used only while $g(x_k) \neq 0$, when $\tilde g_k \neq 0$; if $g(x_k) = 0$ the method stops and the state is repeated.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, pp. 56–57, Theorem 3.3, formulas (3.18)–(3.20)

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), pp. 56–57, Theorem 3.3. Let `x*` be a point, `d > 0`, `S_d = {x : ‖x - x*‖ ≤ d}`,
and let the selection `g` satisfy on `S_d`
`N [f(x) - f(x*)] ≤ (g(x), x - x*) ≤ M [f(x) - f(x*)]` (3.18) with `M > N > 0`.
Run the SDG method with `B₀ = I`, `x₀ ∈ S_d`, stepsizes
`h_{k+1} = (2MN/(M+N)) (f(x_k) - f(x*)) / ‖g̃_k‖` (3.19) and coefficients
`1 < α_{k+1} = α ≤ (M+N)/(M-N)` (3.20). Then `‖A_k (x_k - x*)‖ ≤ d` for `k = 0, 1, 2, …`.
(The book takes `f` almost differentiable, `g` its almost-gradient and `x*` a local minimum;
the proof uses only (3.18), which already forces `f ≥ f(x*)` on `S_d`.) -/
theorem dilated_distance_invariant {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar x₀ : EuclideanSpace ℝ (Fin n)) (d M N α : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hNM : N < M)
    (h318 : ∀ x ∈ Metric.closedBall xstar d,
      N * (f x - f xstar) ≤ inner ℝ (g x) (x - xstar) ∧
        inner ℝ (g x) (x - xstar) ≤ M * (f x - f xstar))
    (hx₀ : x₀ ∈ Metric.closedBall xstar d)
    (hα : 1 < α) (hαMN : α ≤ (M + N) / (M - N)) (k : ℕ) :
    ‖(sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
        (ContinuousLinearEquiv.refl ℝ _) k).A
      ((sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
        (ContinuousLinearEquiv.refl ℝ _) k).x - xstar)‖ ≤ d := by sorry

end ShorNonsmooth.SpaceDilation
