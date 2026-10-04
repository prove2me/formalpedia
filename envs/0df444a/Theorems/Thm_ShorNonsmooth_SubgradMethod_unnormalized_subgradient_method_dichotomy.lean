-- Prove2me | Theorems.Thm_ShorNonsmooth_SubgradMethod_unnormalized_subgradient_method_dichotomy
-- name    : ShorNonsmooth.SubgradMethod.unnormalized_subgradient_method_dichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:03:13.810415+00:00
-- url     : https://prove2.me/theorems/34879f80-274e-4830-8be7-5e075a13b1dd
-- title:
--   Theorem 2.3 — the unnormalized method (2.5) converges iff its subgradients stay bounded
-- statement:
--   Let $f$ be a convex function on $E_n$ whose set $M^*$ of minimum points is nonempty and bounded, $f^* = \min f$, and let $h_k > 0$, $h_k \to 0$, $\sum_{k=1}^\infty h_k = \infty$. From an arbitrary $x_0 \in E_n$ generate
--   $$
--   x_{k+1} = x_k - h_{k+1}\, g_f(x_k), \qquad k = 0, 1, \dots \tag{2.5}
--   $$
--   with any choice of subgradients. Then:
--
--   1. if the sequence $\{g_f(x_k)\}$ is bounded, the method converges:
--   $$
--   \lim_{k \to\infty} \min_{x \in M^*} \|x_k - x\| = 0, \qquad \lim_{k\to\infty} f(x_k) = f^*;
--   $$
--   2. if $\{g_f(x_k)\}$ is unbounded, there is no convergence: the two limits above do not both hold.
--
--   Unlike the normalized method (2.4), the plain method needs bounded subgradients along its trajectory.
--
--   **Formalization Note** The book's "either (a) … or (b) …" is stated as the two implications (bounded ⇒ convergence) and (unbounded ⇒ no convergence), so that neither case holds vacuously. "No convergence" is read as the negation of the convergence statement of (a). Nonemptiness of $M^*$ is explicit, as in Theorem 2.2.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 26, Theorem 2.3

import Mathlib
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod

open Filter Topology

namespace ShorNonsmooth.SubgradMethod

/-- Shor (1985), p. 26, Theorem 2.3. Under the assumptions of Theorem 2.2 (`f` convex on `E_n`,
`M*` nonempty and bounded, `h_k > 0`, `h_k → 0`, `∑_{k≥1} h_k = ∞`), let
`x_{k+1} = x_k - h_{k+1} g_f(x_k)` (2.5) from an arbitrary `x₀`. Then
(a) if `{g_f(x_k)}` is bounded, the method converges:
`min_{x ∈ M*} ‖x_k - x‖ → 0` and `f(x_k) → f*`;
(b) if `{g_f(x_k)}` is unbounded, there is no convergence (the two limits in (a) do not both
hold). -/
theorem unnormalized_subgradient_method_dichotomy {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hMne : (MinSet f).Nonempty)
    (hMbdd : Bornology.IsBounded (MinSet f)) (h : ℕ → ℝ) (hpos : ∀ k, 0 < h (k + 1))
    (hlim : Tendsto h atTop (𝓝 0))
    (hdiv : Tendsto (fun N => ∑ k ∈ Finset.range N, h (k + 1)) atTop atTop)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, ShorNonsmooth.AlmostDiff.IsSubgradient f x (g x)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    (Bornology.IsBounded (Set.range fun k => g (plainIter g h x₀ k)) →
      Tendsto (fun k => Metric.infDist (plainIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
        Tendsto (fun k => f (plainIter g h x₀ k)) atTop (𝓝 (⨅ y, f y))) ∧
    (¬ Bornology.IsBounded (Set.range fun k => g (plainIter g h x₀ k)) →
      ¬ (Tendsto (fun k => Metric.infDist (plainIter g h x₀ k) (MinSet f)) atTop (𝓝 0) ∧
        Tendsto (fun k => f (plainIter g h x₀ k)) atTop (𝓝 (⨅ y, f y)))) := by sorry

end ShorNonsmooth.SubgradMethod
