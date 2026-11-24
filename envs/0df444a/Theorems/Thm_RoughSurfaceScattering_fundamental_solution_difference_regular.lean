-- Prove2me | Theorems.Thm_RoughSurfaceScattering_fundamental_solution_difference_regular
-- name    : RoughSurfaceScattering.fundamental_solution_difference_regular
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T15:55:53.256447+00:00
-- url     : https://prove2.me/theorems/24dbb644-cd7c-4f1b-82f0-cfd7de6b6e5d
-- title:
--   $\Phi_{k_1}(\cdot,y)-\Phi_k(\cdot,y)$ is $C^1$ near $y$ with $L^p$ second derivatives off $y$
-- statement:
--   Let $y\in\mathbb R^2$, $k,k_1\ge0$ and $1\le p<\infty$. There is a function $\tilde D:\mathbb R^2\to\mathbb C$ such that:
--
--   1. $\tilde D(x)=\Phi_{k_1}(x,y)-\Phi_k(x,y)$ for $x\ne y$;
--   2. $\tilde D\in C^1(B_1(y))$;
--   3. each first partial derivative $\partial_i\tilde D$ is differentiable at every $x\in B_1(y)\setminus\{y\}$;
--   4. $\tilde D$, $\partial_i\tilde D$ and $\partial_j\partial_i\tilde D$ (taken off $y$) belong to $L^p(B_1(y))$.
--
--   Writing $\Phi_k(x,y)=a_k(x-y)\,\Phi_0(x,y)+b_k(x-y)$ with smooth $a_k,b_k$ and $a_k(0)=1$, the difference is $(a_{k_1}-a_k)\Phi_0+(b_{k_1}-b_k)$. Here $a_{k_1}-a_k=O(|x-y|^2)$, so the logarithmic singularity is damped: the function is $C^1$ across $y$, and its second derivatives are $O(1+|\ln|x-y||)$, which is $p$-integrable. This is the analytic content of Lemma 5.1.
--
--   **Formalization Note** $\tilde D$ may differ from the platform's value of $\Phi_{k_1}-\Phi_k$ at the single point $x=y$, where the definition uses the convention $\ln0=0$. Derivatives are Fréchet derivatives along the unit vectors $e_i$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Lemma 5.1 and its proof, PDF p. 17 (the logarithmic singularities of Φ_{k_1} and Φ_k cancel; second derivatives are O(|ln|x − y||)).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem fundamental_solution_difference_regular (y : R2) (k k1 : ℝ) (hk : 0 ≤ k) (hk1 : 0 ≤ k1)
    (p : ENNReal) (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    ∃ Dt : R2 → ℂ, (∀ x, x ≠ y → Dt x = Phi k1 x y - Phi k x y) ∧
      ContDiffOn ℝ 1 Dt (Metric.ball y 1) ∧
      (∀ i : Fin 2, ∀ x ∈ Metric.ball y 1, x ≠ y →
        DifferentiableAt ℝ (fun z => fderiv ℝ Dt z (EuclideanSpace.single i 1)) x) ∧
      MemLp Dt p (volume.restrict (Metric.ball y 1)) ∧
      (∀ i : Fin 2, MemLp (fun x => fderiv ℝ Dt x (EuclideanSpace.single i 1)) p
        (volume.restrict (Metric.ball y 1))) ∧
      (∀ i j : Fin 2, MemLp (fun x => fderiv ℝ (fun z => fderiv ℝ Dt z (EuclideanSpace.single i 1))
        x (EuclideanSpace.single j 1)) p (volume.restrict (Metric.ball y 1))) := by sorry

end RoughSurfaceScattering
