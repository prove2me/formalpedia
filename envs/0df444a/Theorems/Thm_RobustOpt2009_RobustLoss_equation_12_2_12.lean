-- Prove2me | Theorems.Thm_RobustOpt2009_RobustLoss_equation_12_2_12
-- name    : RobustOpt2009.RobustLoss.equation_12_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:30.43587+00:00
-- url     : https://prove2.me/theorems/7313c374-5a7a-465c-bc25-6a8da135b0e8
-- title:
--   Equation 12.2.12 — additive uncertainty and the support function
-- statement:
--   Let $n,\ell,m\ge1$, $Z^n\in\mathbb R^{n\times m}$, $U\in\mathbb R^{n\times\ell}$, $\rho\ge0$, and let $D\subset\mathbb R^{\ell\times m}$ be convex, compact and contain zero. Write $r=(Z^n)^T\theta$ and $u=U^T\theta$. Let $L:\mathbb R^m\to\mathbb R$ be convex and satisfy Assumption L: $L(x)=\pi(|x|)$ for every $x$, or $L(x)=\pi(x_+)$ for every $x$, where $\pi$ is convex and coordinatewise nondecreasing on the nonnegative orthant. Write $L^*(v)=\sup_x(v^Tx-L(x))$, which can equal $+\infty$.
--
--   For every $\theta\in\mathbb R^n$, all three following maxima exist, have a common finite value, and satisfy
--   $$\max_{\Delta\in D}L((Z^n+\rho U\Delta)^T\theta)=\max_{\Delta\in D,v}\{v^T(Z^n+\rho U\Delta)^T\theta-L^*(v)\}=\max_v\{v^Tr-L^*(v)+\rho\max_{\Delta\in D}\theta^TU\Delta v\}.$$
--   This is the support-function identity for additive data uncertainty.
--
--   **Formalization Note** Maxima are expressed with `IsGreatest`, retaining attainment. The inner real supremum is over a nonempty compact image and is therefore finite and attained. All remaining dual values lie in `EReal`; finite terms minus $+\infty$ equal $-\infty$.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Equation 12.2.12, printed p. 316 (PDF p. 342).

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace
open ConvexOptimization

namespace RobustOpt2009.RobustLoss

/-- Ben-Tal, El Ghaoui and Nemirovski (2009), printed p. 316, PDF p. 342.
The imported Fenchel conjugate is `L*(v) = sup_x (inner x v - L x)` in EReal.
All finite-dimensional vectors use their usual real coordinates. The norm of the
plain coordinate function in the goal is the infinity norm, not the Euclidean norm.
The existential function π is constrained only on the nonnegative orthant.
Computational tractability is relative to evaluation of the supplied functions;
no machine-cost model is asserted. -/
theorem equation_12_2_12
    {n l m : ℕ} (hn : 0 < n) (hl : 0 < l) (hm : 0 < m)
    (Zn : Matrix (Fin n) (Fin m) ℝ) (U : Matrix (Fin n) (Fin l) ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (D : Set (Matrix (Fin l) (Fin m) ℝ))
    (hDc : Convex ℝ D) (hDk : IsCompact D) (hD0 : 0 ∈ D)
    (L : EuclideanSpace ℝ (Fin m) → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hL : ∃ π : EuclideanSpace ℝ (Fin m) → ℝ,
      ConvexOn ℝ {x | ∀ i, 0 ≤ x i} π ∧
      (∀ x y, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ y i) → π x ≤ π y) ∧
      ((∀ r, L r = π (WithLp.toLp 2 (fun i => |r i|))) ∨
       (∀ r, L r = π (WithLp.toLp 2 (fun i => max (r i) 0)))))
    (θ : EuclideanSpace ℝ (Fin n)) :
    ∃ M : ℝ,
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        L (WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a))) '' D) M ∧
      IsGreatest {w : EReal | ∃ Δ ∈ D, ∃ v : EuclideanSpace ℝ (Fin m),
        w = ((⟪(WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a)), v⟫ : ℝ) : EReal) - fenchelConjugate L v} (M : EReal) ∧
      IsGreatest (Set.range (fun v : EuclideanSpace ℝ (Fin m) =>
        (((⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a)), v⟫ : ℝ) + ρ * sSup ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
          ∑ a, ∑ b, ∑ i, θ a * U a b * Δ b i * v i) '' D) : ℝ) : EReal) -
          fenchelConjugate L v)) (M : EReal) := by sorry

end RobustOpt2009.RobustLoss
