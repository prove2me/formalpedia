-- Prove2me | Theorems.Thm_StochOptForest_ApxRisk_theorem_9_uniform
-- name    : StochOptForest.ApxRisk.theorem_9_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:02.59544+00:00
-- url     : https://prove2.me/theorems/9f9e8d58-56f0-4fb8-826b-e5d1319e406b
-- title:
--   Proof of Theorem 2, p. 81 — Theorem 9 uniformly over base functions near f̄ (the uniformity the proof uses)
-- statement:
--   Let $\bar f:\mathbb R^d\to\mathbb R$ be twice continuously differentiable with a unique minimizer $\bar z$, $\nabla^2\bar f(\bar z)$ positive definite, and a bounded sublevel set $\{z:\bar f(z)\le\alpha\}$ for some $\alpha>\bar f(\bar z)$. Then for every $\varepsilon>0$ there is $\eta>0$ with the following property. Let $f_0$ be twice continuously differentiable with $\|f_0-\bar f\|_{\mathcal F}\le\eta$, with a unique minimizer $z_0$ at which $\nabla^2 f_0$ is positive definite, and let $\delta_f$ be twice continuously differentiable with $\|\delta_f\|_{\mathcal F}\le N\le\eta$. Then
--   $$\Bigl|\min_{z}\bigl(f_0+\delta_f\bigr)(z)-f_0(z_0)-\delta_f(z_0)+\frac12\nabla\delta_f(z_0)^\top\bigl(\nabla^2 f_0(z_0)\bigr)^{-1}\nabla\delta_f(z_0)\Bigr|\le\varepsilon N^2 .$$
--
--   The proof of Theorem 2 applies Theorem 9 with base function $f_0$, the average cost over the region $R_0$, which changes as $R_0$ shrinks, and then lets the diameter go to $0$. That step needs the $o(\|\delta_f\|^2_{\mathcal F})$ of Theorem 9 to hold uniformly over base functions close to a fixed nondegenerate limit $\bar f$; this statement provides it.
--
--   **Formalization Note** The paper does not state this uniformity; the proof on p. 81 uses it where it applies Theorem 9 for $j=1,2$. Hessian closeness is in operator norm.
-- source:
--   Kallus & Mao, arXiv:2008.07473v6, p. 81, Proof for Theorem 2 (application of Theorem 9, p. 65)

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model

namespace StochOptForest.ApxRisk

theorem theorem_9_uniform {d : ℕ} (fbar : Ed d → ℝ) (zbar : Ed d) (hfbar : ContDiff ℝ 2 fbar)
    (hmin : IsUniqueMin fbar zbar) (hpd : PosDefAt fbar zbar)
    (hlev : ∃ α : ℝ, fbar zbar < α ∧ Bornology.IsBounded {z | fbar z ≤ α}) :
    ∀ ε > 0, ∃ η > 0, ∀ (f0 : Ed d → ℝ) (z0 : Ed d), ContDiff ℝ 2 f0 →
      FNormLE (fun z => f0 z - fbar z) η → IsUniqueMin f0 z0 → PosDefAt f0 z0 →
      ∀ N : ℝ, N ≤ η → ∀ δf : Ed d → ℝ, ContDiff ℝ 2 δf → FNormLE δf N →
        |optVal (fun z => f0 z + δf z) - f0 z0 - δf z0
          + (1 / 2) * newtonQuad f0 δf z0| ≤ ε * N ^ 2 := by sorry

end StochOptForest.ApxRisk
