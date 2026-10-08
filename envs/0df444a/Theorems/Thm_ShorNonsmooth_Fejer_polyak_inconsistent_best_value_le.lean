-- Prove2me | Theorems.Thm_ShorNonsmooth_Fejer_polyak_inconsistent_best_value_le
-- name    : ShorNonsmooth.Fejer.polyak_inconsistent_best_value_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T12:31:15.403996+00:00
-- url     : https://prove2.me/theorems/cf14282a-bd90-438f-a729-e43e505eec46
-- title:
--   Theorem 2.14 — with $c = 0$ below the minimum $d$, the best value tends to at most $2d/(2-\gamma)$
-- statement:
--   Let $\psi$ be convex on $E_n$ with $\min_{x \in E_n} \psi(x) = d > 0$, let $0 < \gamma < 2$, and let $\{x_k\}$ be generated from a starting point $x_0$ by
--   $$
--   x_{k+1} = x_k - \frac{\gamma\,\psi(x_k)}{\|g_\psi(x_k)\|^2}\, g_\psi(x_k),
--   $$
--   that is, Polyak's method (2.32) with the level $c = 0$ lying below the minimum value, for any subgradient selection $g_\psi$. Then the limit of the best values found exists and satisfies
--   $$
--   \lim_{k \to \infty} \min_{0 \le i \le k} \psi(x_i) \le \frac{2d}{2 - \gamma} .
--   $$
--
--   This is the situation of an inconsistent system of convex inequalities $f_i(x) \le 0$ with $\psi = \max_i f_i^+$: the method run with the wrong level still produces points whose value is within the factor $2/(2-\gamma)$ of the optimum.
--
--   **Formalization Note** The book prints "$= 2d/(2-\gamma)$"; its proof (pp. 39–40) establishes only "$\le$", and equality fails, e.g. for $\psi(x) = \max(d, d + x)$ on $\mathbb{R}$ with $x_0 = 0$, $g_\psi(0) = 1$. The statement is the inequality the proof gives. If $g_\psi(x_k) = 0$ (so $x_k$ is a minimum point) the book's formula is undefined; the method then stops at $x_k$. The best value is the minimum over the finite set $\{0, \dots, k\}$.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 40, Theorem 2.14 (proof pp. 39–40)

import Mathlib
import Definitions.Def_ShorNonsmooth_Fejer_PolyakMethod

open Filter Topology

namespace ShorNonsmooth.Fejer

/-- Shor (1985), p. 40, Theorem 2.14, in the form its proof (pp. 39–40) establishes. Let `ψ` be
convex on `E_n` with `min_{x ∈ E_n} ψ(x) = d > 0`, let `0 < γ < 2`, and let `{x_k}` be generated
from `x₀` by `x_{k+1} = x_k - γ ψ(x_k) / ‖g_ψ(x_k)‖² · g_ψ(x_k)` (Polyak's method (2.32) with
`c = 0`; the method stops if `g_ψ(x_k) = 0`), for any subgradient selection `g_ψ`. Then the limit
`lim_{k→∞} min_{0 ≤ i ≤ k} ψ(x_i)` exists and is at most `2d / (2 - γ)`.

The book prints "`= 2d/(2 - γ)`"; its proof gives only `≤`, and equality can fail. -/
theorem polyak_inconsistent_best_value_le {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ConvexOn ℝ Set.univ ψ) (d : ℝ) (hd : 0 < d) (hdle : ∀ y, d ≤ ψ y)
    (hdatt : ∃ xm, ψ xm = d) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient ψ x (g x))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : ∀ k, x (k + 1) = polyakStep ψ g 0 γ (x k)) :
    ∃ ℓ : ℝ, Tendsto (fun k : ℕ =>
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (fun i => ψ (x i)))
        atTop (𝓝 ℓ) ∧ ℓ ≤ 2 * d / (2 - γ) := by sorry

end ShorNonsmooth.Fejer
