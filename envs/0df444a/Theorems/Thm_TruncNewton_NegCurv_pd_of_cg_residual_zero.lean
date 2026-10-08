-- Prove2me | Theorems.Thm_TruncNewton_NegCurv_pd_of_cg_residual_zero
-- name    : TruncNewton.NegCurv.pd_of_cg_residual_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:18.725035+00:00
-- url     : https://prove2.me/theorems/b5d8b8dc-9a3b-44fa-82ab-d9b91ea38130
-- title:
--   Proof of Theorem 2.4, p. 211 — if g meets every eigenspace of H and exact CG ends with r = 0, then H is positive definite
-- statement:
--   Let $H$ be a symmetric linear operator on $\mathbb{R}^n$ and $g\in\mathbb{R}^n$, and run the TNCG minor iteration (Steps 1–4, p. 194) with $\varepsilon=\eta=0$, producing directions $d_j$ and residuals $r_j$. Suppose that $g$ is not orthogonal to any eigenspace of $H$, i.e. for every eigenvalue $\mu$ of $H$ there is $v$ with $Hv=\mu v$ and $g^{\mathsf T}v\ne0$. Suppose further that for some $i\ge0$ the curvature test (2.1) with $\varepsilon=0$ passes at every iteration up to $i$,
--
--   $$
--   d_j^{\mathsf T}Hd_j>0,\qquad j=0,1,\dots,i,
--   $$
--
--   and that the iteration then ends with zero residual, $r_{i+1}=0$ (the test (2.2) with $\eta=0$). Then $H$ is positive definite:
--
--   $$
--   v^{\mathsf T}Hv>0\qquad\text{for all } v\ne0 .
--   $$
--
--   This is the first sentence of the proof of Theorem 2.4, obtained there from Theorem A.5 together with (A.2) and (A.5); it says that exact CG can only end with $r=0$ at a non-convex point when $g$ misses some eigenspace.
--
--   **Formalization Note** "$r=0$" is encoded as $r_{i+1}=0$ after $i+1$ CG steps whose curvature was positive at every step, which is exactly the exit through (2.2) with $\eta=0$ at iteration $i$. $H$ symmetric is the paper's standing setting ($H$ is a Hessian).
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 211, proof of Theorem 2.4, first sentence

import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem pd_of_cg_residual_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (i : ℕ) (hcurv : ∀ j ≤ i, 0 < inner ℝ ((cg H g j).d) (H (cg H g j).d))
    (hr : (cg H g (i + 1)).r = 0) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by sorry

end TruncNewton.NegCurv
