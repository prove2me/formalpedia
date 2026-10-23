-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_corollary_1
-- name    : StochOptForest.ApxRisk.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:11.26092+00:00
-- url     : https://prove2.me/theorems/9b688ea8-eea9-4b09-90ed-b5f71dab32f8
-- title:
--   Corollary 1, p. 64 — second-order expansion of the optimal value and first-order expansion of the minimizer of f + tδ_f as t ↓ 0
-- statement:
--   Let $f,\delta_f:\mathbb R^d\to\mathbb R$ and consider the perturbed problem (67)
--   $$v(t)=\min_{z\in\mathbb R^d} f(z)+t\delta_f(z).$$
--   Suppose that:
--
--   1. $f$ is twice continuously differentiable and $\delta_f$ is continuously differentiable;
--   2. there are a constant $\alpha$, a constant $t_0\in(0,1]$ and a compact set $\overline C\subseteq\mathbb R^d$ such that for every $t\in[0,t_0)$ the sublevel set $\{z: f(z)+t\delta_f(z)\le\alpha\}$ is nonempty and contained in $\overline C$;
--   3. $f$ has a unique minimizer $z^*$ over $\mathbb R^d$ and $\nabla^2 f(z^*)$ is positive definite.
--
--   Then, as $t\downarrow0$,
--   $$v(t)=v(0)+t\delta_f(z^*)-\frac12t^2\nabla\delta_f(z^*)^\top\bigl(\nabla^2f(z^*)\bigr)^{-1}\nabla\delta_f(z^*)+o(t^2), \tag{68}$$
--   and every optimal solution $z^*(t)$ of the perturbed problem satisfies
--   $$z^*(t)=z^*-t\bigl(\nabla^2f(z^*)\bigr)^{-1}\nabla\delta_f(z^*)+o(t).$$
--
--   With $f=f_0$ and $\delta_f=f_j-f_0$ this is Theorem 1, the second-order perturbation analysis behind the approximate splitting criteria.
--
--   **Formalization Note** Both $o(\cdot)$ claims are stated in $\varepsilon$–$\delta$ form for $t\in(0,t_1)$; $v(t)$ is the real infimum, attained for $t<t_0$ by condition 2.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 64, Corollary 1 and eq. (67)–(68) (proof p. 74)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

theorem corollary_1 {d : ℕ} (f δf : Ed d → ℝ) (zs : Ed d)
    (hf : ContDiff ℝ 2 f) (hδf : ContDiff ℝ 1 δf)
    (hcond2 : ∃ α t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ ∃ C : Set (Ed d), IsCompact C ∧
      ∀ t ∈ Set.Ico (0 : ℝ) t0,
        {z | f z + t * δf z ≤ α}.Nonempty ∧ {z | f z + t * δf z ≤ α} ⊆ C)
    (hmin : IsUniqueMin f zs) (hpd : PosDefAt f zs) :
    (∀ ε > 0, ∃ t1 > 0, ∀ t ∈ Set.Ioo (0 : ℝ) t1,
      |optVal (fun z => f z + t * δf z) - optVal f - t * δf zs
        + (1 / 2) * t ^ 2 * newtonQuad f δf zs| ≤ ε * t ^ 2) ∧
    (∀ ε > 0, ∃ t1 > 0, ∀ t ∈ Set.Ioo (0 : ℝ) t1, ∀ z : Ed d,
      (∀ w, f z + t * δf z ≤ f w + t * δf w) →
      ‖z - (zs - t • (hess f zs).inverse (gradient δf zs))‖ ≤ ε * t) := by sorry

end StochOptForest.ApxRisk
