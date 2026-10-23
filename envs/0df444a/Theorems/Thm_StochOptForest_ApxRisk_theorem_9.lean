-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_theorem_9
-- name    : StochOptForest.ApxRisk.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:09.591875+00:00
-- url     : https://prove2.me/theorems/36b0e4bc-f88b-461c-86e1-8425f4ed679d
-- title:
--   Theorem 9, p. 65 — expansion of v(f₀ + δ_f) and z*(f₀ + δ_f) with errors o(‖δ_f‖²_F) and o(‖δ_f‖_F)
-- statement:
--   Let $f_0:\mathbb R^d\to\mathbb R$ be twice continuously differentiable with a unique minimizer $z^*(f_0)$ at which $\nabla^2 f_0$ is positive definite. Write $v(f)=\min_z f(z)$ and $z^*(f)$ for a minimizer (eq. (69)), and $\|\cdot\|_{\mathcal F}$ for the norm (70). Consider twice continuously differentiable perturbations $\delta_f$ such that
--
--   1. condition 2 of Corollary 1 holds for $t\in[0,1]$: for some $\alpha$ and compact $\overline C$, every sublevel set $\{z:f_0(z)+t\delta_f(z)\le\alpha\}$, $t\in[0,1]$, is nonempty and contained in $\overline C$;
--   2. for every $t\in[0,1]$, $f_0+t\delta_f$ has a unique minimizer $z^*(f_0+t\delta_f)$ at which its Hessian is positive definite.
--
--   Then, as $\|\delta_f\|_{\mathcal F}\to0$,
--   $$v(f_0+\delta_f)=v(f_0)+\delta_f(z^*(f_0))-\frac12\nabla\delta_f(z^*(f_0))^\top\bigl(\nabla^2f_0(z^*(f_0))\bigr)^{-1}\nabla\delta_f(z^*(f_0))+o(\|\delta_f\|^2_{\mathcal F}),$$
--   $$z^*(f_0+\delta_f)=z^*(f_0)-\bigl(\nabla^2f_0(z^*(f_0))\bigr)^{-1}\nabla\delta_f(z^*(f_0))+o(\|\delta_f\|_{\mathcal F}).$$
--   Explicitly: for every $\varepsilon>0$ there is $\eta>0$ such that, whenever $\|\delta_f\|_{\mathcal F}\le N\le\eta$ and $\delta_f$ satisfies 1–2, the value error is at most $\varepsilon N^2$ and the solution error at most $\varepsilon N$.
--
--   This turns the directional expansion of Corollary 1 into one whose error is controlled by the size of the perturbation, which is what makes the criteria accurate for small regions.
--
--   **Formalization Note** The page writes $\nabla^2f(z^*(f_0))$ for $\nabla^2f_0(z^*(f_0))$. The hypotheses are kept as printed; the uniqueness of the minimizer for every $t\in[0,1]$ is essential (without it the expansion fails for perturbations that create a distant competing minimum). Hessians are bounded in operator norm rather than Frobenius norm, which only weakens the hypothesis $\|\delta_f\|_{\mathcal F}\le N$.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 65, Theorem 9 and eqs. (69)–(70) (proof pp. 74–75)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

theorem theorem_9 {d : ℕ} (f0 : Ed d → ℝ) (zs : Ed d) (hf0 : ContDiff ℝ 2 f0)
    (hmin : IsUniqueMin f0 zs) (hpd : PosDefAt f0 zs) :
    ∀ ε > 0, ∃ η > 0, ∀ N : ℝ, N ≤ η → ∀ δf : Ed d → ℝ, ContDiff ℝ 2 δf → FNormLE δf N →
      (∃ α : ℝ, ∃ C : Set (Ed d), IsCompact C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
        {z | f0 z + t * δf z ≤ α}.Nonempty ∧ {z | f0 z + t * δf z ≤ α} ⊆ C) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ zt : Ed d, IsUniqueMin (fun z => f0 z + t * δf z) zt ∧
        PosDefAt (fun z => f0 z + t * δf z) zt) →
      |optVal (fun z => f0 z + δf z) - optVal f0 - δf zs
          + (1 / 2) * newtonQuad f0 δf zs| ≤ ε * N ^ 2 ∧
      ∀ z1 : Ed d, IsUniqueMin (fun z => f0 z + δf z) z1 →
        ‖z1 - (zs - (hess f0 zs).inverse (gradient δf zs))‖ ≤ ε * N := by sorry

end StochOptForest.ApxRisk
