-- Prove2me | Theorems.Thm_TruncNewton_NegCurv_theorem_2_4
-- name    : TruncNewton.NegCurv.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:07:29.969078+00:00
-- url     : https://prove2.me/theorems/c6afa168-b38d-480f-8236-4e0609611670
-- title:
--   Theorem 2.4, p. 197 — with ηₖ = ε = 0, exact CG meets dᵢᵀHdᵢ ≤ 0 unless g is orthogonal to the nonpositive eigenspaces of H
-- statement:
--   Let $H$ be a symmetric linear operator on $\mathbb{R}^n$ (the Hessian $H(x_k)$ at a major iterate) and $g\in\mathbb{R}^n$ (the gradient $g(x_k)$). Run the TNCG minor iteration (Steps 1–4, p. 194) with $\eta_k=\varepsilon=0$ in (2.1) and (2.2): the curvature test is $d_i^{\mathsf T}Hd_i\le0$ and the truncation test is $r_{i+1}=0$.
--
--   **Theorem 2.4.** If $H$ is not positive definite, then
--
--   1. either the minor iteration reaches some iteration $i$ (no test fired at any earlier iteration) with
--   $$
--   d_i^{\mathsf T}Hd_i\le 0,
--   $$
--   i.e. it exits through (2.1) at $i$;
--   2. or $g$ is orthogonal to the eigenspaces of $H$ corresponding to the nonpositive eigenvalues: $g^{\mathsf T}v=0$ whenever $Hv=\mu v$ with $\mu\le0$.
--
--   The theorem justifies using the direction of negative curvature $d_i$ to move away from stationary points that are not local minimizers: exact CG detects nonpositive curvature except in the rare case in which $g$ has no component along a nonpositive eigenspace.
--
--   **Formalization Note** The page's theorem is about $H(x_k)$ and $g(x_k)$ at an iterate of the TNCG run, but uses nothing about the objective or the run, and every symmetric $H$ and every $g$ occur as Hessian and gradient at a point of an admissible objective (a quadratic, modified far away so that its level sets are bounded). The statement is therefore made for an arbitrary symmetric (self-adjoint) $H$ and vector $g$. The first alternative requires that iteration $i$ is actually reached (no earlier exit): a bare "$d_i^{\mathsf T}Hd_i\le0$ for some $i$" over the unstopped recursion would be trivially true after a zero residual, where the recursion continues with $d=0$. For $\mu$ that is not an eigenvalue only $v=0$ satisfies $Hv=\mu v$, so the second alternative quantifies over all $\mu\le0$ without an eigenvalue predicate.
-- source:
--   Dembo and Steihaug, Truncated-Newton algorithms for large-scale unconstrained optimization, Math. Programming 26 (1983), p. 197, Theorem 2.4

import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting

namespace TruncNewton.NegCurv

theorem theorem_2_4 {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hnpd : ¬ ∀ v, v ≠ 0 → 0 < inner ℝ v (H v)) :
    (∃ i, ExitsVia21 H g 0 0 i) ∨
      (∀ μ : ℝ, μ ≤ 0 → ∀ v, H v = μ • v → inner ℝ g v = 0) := by sorry

end TruncNewton.NegCurv
