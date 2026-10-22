-- Prove2me | Theorems.Thm_RobustOpt2009_RobustLoss_theorem_12_2_5
-- name    : RobustOpt2009.RobustLoss.theorem_12_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:32.75609+00:00
-- url     : https://prove2.me/theorems/c7479fed-fa23-45dd-b62f-72b31c8a8f06
-- title:
--   Theorem 12.2.5 — finite reformulation for the infinity norm
-- statement:
--   Let $n,\ell,m\ge1$, $Z^n\in\mathbb R^{n\times m}$, $U\in\mathbb R^{n\times\ell}$, $\rho\ge0$, and let $D\subset\mathbb R^{\ell\times m}$ be convex, compact and contain zero. Write $r=(Z^n)^T\theta$ and $u=U^T\theta$. Let $L:\mathbb R^m\to\mathbb R$ be convex and satisfy Assumption L: $L(x)=\pi(|x|)$ for every $x$, or $L(x)=\pi(x_+)$ for every $x$, where $\pi$ is convex and coordinatewise nondecreasing on the nonnegative orthant. Write $L^*(v)=\sup_x(v^Tx-L(x))$, which can equal $+\infty$.
--
--   Assumption A means that a finite nonnegative convex positively homogeneous function $\phi$ and a norm $\psi$ satisfy $\max_{\Delta\in D}u^T\Delta v=\phi(u)\psi(v)$ for every $u,v$. Fix $\psi(v)=\|v\|_\infty$ and any $\tau\in\mathbb R$. For every $\theta$, the following are equivalent:
--   $$\forall\Delta\in D:\ L((Z^n+\rho U\Delta)^T\theta)\le\tau;$$
--   $$\exists\kappa\in\mathbb R:\quad \rho\phi(U^T\theta)\le\kappa,\qquad L((Z^n)^T\theta+\kappa e_i)\le\tau,\quad L((Z^n)^T\theta-\kappa e_i)\le\tau\quad(1\le i\le m).$$
--   The left-hand functions defining these $2m+1$ inequalities, namely $\rho\phi(U^T\theta)-\kappa$ and the two shifted losses for every $i$, are convex in $(\theta,\kappa)$.
--
--   This is the finite convex reformulation of Theorem 12.2.5.
--
--   **Formalization Note** The coordinates are zero-indexed `Fin m`; both signs are required for every coordinate. The amplitude lower bound implies $\kappa\ge0$. Quantification over $\Delta$ exactly parametrizes $\mathcal Z=Z^n+\rho UD$, without any injectivity requirement. Computational tractability is represented by the explicit finite formulas relative to evaluation of $L$ and $\phi$; no bit-complexity or oracle implementation is asserted. Assumption L is retained in full, and convexity of $L$ is also listed as in the standing setup on printed p. 311.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Theorem 12.2.5, printed p. 319 (PDF p. 345).

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace
open ConvexOptimization

namespace RobustOpt2009.RobustLoss

/-- Ben-Tal, El Ghaoui and Nemirovski (2009), printed p. 319, PDF p. 345.
The imported Fenchel conjugate is `L*(v) = sup_x (inner x v - L x)` in EReal.
All finite-dimensional vectors use their usual real coordinates. The norm of the
plain coordinate function in the goal is the infinity norm, not the Euclidean norm.
The existential function π is constrained only on the nonnegative orthant.
Computational tractability is relative to evaluation of the supplied functions;
no machine-cost model is asserted. -/
theorem theorem_12_2_5
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
    (φ : EuclideanSpace ℝ (Fin l) → ℝ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hφc : ConvexOn ℝ Set.univ φ)
    (hφh : ∀ t : ℝ, 0 ≤ t → ∀ u, φ (t • u) = t * φ u)
    (hA : ∀ (u : EuclideanSpace ℝ (Fin l)) (v : EuclideanSpace ℝ (Fin m)),
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        ∑ a, ∑ i, u a * Δ a i * v i) '' D) (φ u * ‖(fun i => v i)‖))
    (τ : ℝ) :
    (∀ θ : EuclideanSpace ℝ (Fin n),
      (∀ Δ ∈ D, L (WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a)) ≤ τ) ↔
      ∃ κ : ℝ, ρ * φ (WithLp.toLp 2 (fun b => ∑ a, U a b * θ a)) ≤ κ ∧
        ∀ i : Fin m, L (WithLp.toLp 2 (fun j => (∑ a, Zn a j * θ a) + if j = i then κ else 0)) ≤ τ ∧
          L (WithLp.toLp 2 (fun j => (∑ a, Zn a j * θ a) - if j = i then κ else 0)) ≤ τ) ∧
    ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      ρ * φ (WithLp.toLp 2 (fun b => ∑ a, U a b * p.1 a)) - p.2) ∧
    (∀ i : Fin m,
      ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        L (WithLp.toLp 2 (fun j => (∑ a, Zn a j * p.1 a) + if j = i then p.2 else 0))) ∧
      ConvexOn ℝ Set.univ (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
        L (WithLp.toLp 2 (fun j => (∑ a, Zn a j * p.1 a) - if j = i then p.2 else 0)))) := by sorry

end RobustOpt2009.RobustLoss
