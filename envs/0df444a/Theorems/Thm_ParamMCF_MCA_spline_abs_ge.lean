-- Prove2me | Theorems.Thm_ParamMCF_MCA_spline_abs_ge
-- name    : ParamMCF.MCA.spline_abs_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:21.450281+00:00
-- url     : https://prove2.me/theorems/981fc318-1bf6-482a-9ad2-b1d05fe0ea13
-- title:
--   Proof of Theorem 5, p. 18 — under (ii) the linear spline dominates the marginal cost in absolute value
-- statement:
--   Let $f$ be a marginal cost (strictly increasing, differentiable, $f(s)\le0$ for $s<0$ and $f(s)\ge0$ for $s>0$) whose first and second derivatives are differentiable, and assume the shape condition of Theorem 5 (ii): $f''$ is non-decreasing with $f''\ge0$ on $[0,\infty)$, and non-increasing with $f''\le0$ on $(-\infty,0)$. Let $-x^{\max}=x_0<x_1<\dots<x_K=x^{\max}$ be a mesh having $0$ as one of its points, and let $s_f$ be the linear spline of $f$ on it. Then
--
--   $$|s_f(x)|\ge|f(x)|\qquad\text{for all }x\in[-x^{\max},x^{\max}].$$
--
--   In the proof of Theorem 5 this verifies the side condition $|\widetilde f_e|\ge|f_e|$ of Lemma 4's second case for $\widetilde f_e=s_{f_e}$.
--
--   **Formalization Note** The paper writes "for all $x\in\mathbb R$" but defines $s_f$ only on the mesh interval; the Lean spline extends its end chords linearly, and beyond $x^{\max}$ the extended chord of a convex $f$ lies below $f$, so the claim is stated on $[-x^{\max},x^{\max}]$. The requirement that $0$ be a mesh point is the correction made in Theorem 5; without it a chord straddling $0$ can violate the inequality. The mesh is indexed $x_0,\dots,x_K$.
-- source:
--   Joachims, Klimm & Warode, Approximate Parametric Computation of Minimum-Cost Flows with Convex Costs, arXiv:2203.13146v1, p. 18, proof of Theorem 5, case (ii)

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model

namespace ParamMCF.MCA

/-- Proof of Theorem 5, p. 18: under the shape condition of (ii), the linear spline of a marginal
cost on a mesh of `[-X, X]` having `0` as a mesh point dominates it in absolute value on `[-X, X]`. -/
theorem spline_abs_ge (g : ℝ → ℝ) (hg : IsMarginalCost g)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0))
    (X : ℝ) (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (hfirst : xs 0 = -X) (hlast : xs (Fin.last K) = X) (hzero : ∃ j, xs j = 0) :
    ∀ x ∈ Set.Icc (-X) X, |g x| ≤ |linSpline K xs g x| := by sorry

end ParamMCF.MCA
