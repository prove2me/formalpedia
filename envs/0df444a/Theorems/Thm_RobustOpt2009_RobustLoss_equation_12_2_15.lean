-- Prove2me | Theorems.Thm_RobustOpt2009_RobustLoss_equation_12_2_15
-- name    : RobustOpt2009.RobustLoss.equation_12_2_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:38.083265+00:00
-- url     : https://prove2.me/theorems/2302b9d9-69b1-43dd-8542-76a73f4301d6
-- title:
--   Equation 12.2.15 — factorized worst-case realized loss
-- statement:
--   Let $n,\ell,m\ge1$, $Z^n\in\mathbb R^{n\times m}$, $U\in\mathbb R^{n\times\ell}$, $\rho\ge0$, and let $D\subset\mathbb R^{\ell\times m}$ be convex, compact and contain zero. Write $r=(Z^n)^T\theta$ and $u=U^T\theta$. Let $L:\mathbb R^m\to\mathbb R$ be convex and satisfy Assumption L: $L(x)=\pi(|x|)$ for every $x$, or $L(x)=\pi(x_+)$ for every $x$, where $\pi$ is convex and coordinatewise nondecreasing on the nonnegative orthant. Write $L^*(v)=\sup_x(v^Tx-L(x))$, which can equal $+\infty$.
--
--   Assumption A means that a finite nonnegative convex positively homogeneous function $\phi$ and a norm $\psi$ satisfy $\max_{\Delta\in D}u^T\Delta v=\phi(u)\psi(v)$ for every $u,v$.
--
--   For every $\theta$, both maxima are attained and have the same finite value:
--   $$\max_{\Delta\in D}L((Z^n+\rho U\Delta)^T\theta)=\max_v\{v^Tr-L^*(v)+\rho\phi(u)\psi(v)\}.$$
--   This identity isolates the parameter-dependent uncertainty amplitude.
--
--   **Formalization Note** `IsGreatest` expresses both equality and attainment at a common real value. The gauge and norm axioms and the rank-one support identity are explicit hypotheses; no worst-case representation is assumed.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Equation 12.2.15, printed p. 318 (PDF p. 344).

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace
open ConvexOptimization

namespace RobustOpt2009.RobustLoss

/-- Ben-Tal, El Ghaoui and Nemirovski (2009), printed p. 318, PDF p. 344.
The imported Fenchel conjugate is `L*(v) = sup_x (inner x v - L x)` in EReal.
All finite-dimensional vectors use their usual real coordinates. The norm of the
plain coordinate function in the goal is the infinity norm, not the Euclidean norm.
The existential function π is constrained only on the nonnegative orthant.
Computational tractability is relative to evaluation of the supplied functions;
no machine-cost model is asserted. -/
theorem equation_12_2_15
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
    (ψ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hψ0 : ∀ v, 0 ≤ ψ v) (hψz : ∀ v, ψ v = 0 ↔ v = 0)
    (hψh : ∀ (t : ℝ) v, ψ (t • v) = |t| * ψ v)
    (hψa : ∀ v w, ψ (v + w) ≤ ψ v + ψ w)
    (hA : ∀ (u : EuclideanSpace ℝ (Fin l)) (v : EuclideanSpace ℝ (Fin m)),
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        ∑ a, ∑ i, u a * Δ a i * v i) '' D) (φ u * ψ v))
    (θ : EuclideanSpace ℝ (Fin n)) :
    ∃ M : ℝ,
      IsGreatest ((fun Δ : Matrix (Fin l) (Fin m) ℝ =>
        L (WithLp.toLp 2 (fun i => ∑ a, (Zn a i + ρ * ∑ b, U a b * Δ b i) * θ a))) '' D) M ∧
      IsGreatest (Set.range (fun v : EuclideanSpace ℝ (Fin m) =>
        (((⟪(WithLp.toLp 2 (fun i => ∑ a, Zn a i * θ a)), v⟫ : ℝ) + ρ * φ (WithLp.toLp 2 (fun b => ∑ a, U a b * θ a)) * ψ v : ℝ) : EReal) -
          fenchelConjugate L v)) (M : EReal) := by sorry

end RobustOpt2009.RobustLoss
