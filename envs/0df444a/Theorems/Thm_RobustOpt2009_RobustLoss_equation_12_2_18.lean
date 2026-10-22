-- Prove2me | Theorems.Thm_RobustOpt2009_RobustLoss_equation_12_2_18
-- name    : RobustOpt2009.RobustLoss.equation_12_2_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:34.191556+00:00
-- url     : https://prove2.me/theorems/0066978b-aa9b-489b-abc1-dbc2783ef7bb
-- title:
--   Equation 12.2.18 — dual-norm-ball representation
-- statement:
--   Let $m\ge1$ and let the finite convex loss $L:\mathbb R^m\to\mathbb R$ satisfy Assumption L: it has the form $\pi(|x|)$ or $\pi(x_+)$, with $\pi$ convex and coordinatewise nondecreasing on the nonnegative orthant. Let $\psi$ be any norm on $\mathbb R^m$, $r\in\mathbb R^m$, and $\kappa\ge0$. Let $L^*(v)=\sup_x(v^Tx-L(x))$. Both maxima exist, are finite and equal:
--   $$L_{\rm wc}(r,\kappa):=\max_v\{v^Tr-L^*(v)+\kappa\psi(v)\}=\max_{\psi^*(\xi)\le1}L(r+\kappa\xi).$$
--   This is the residual-perturbation representation of worst-case loss.
--
--   **Formalization Note** The dual unit ball is defined directly by $\xi^Tv\le\psi(v)$ for every $v$, equivalently $\psi^*(\xi)\le1$. A common real `IsGreatest` value retains attainment on both sides. No data matrices are needed for this identity.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Equation 12.2.18, printed p. 318 (PDF p. 344).

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
theorem equation_12_2_18
    {m : ℕ} (hm : 0 < m)
    (L : EuclideanSpace ℝ (Fin m) → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hL : ∃ π : EuclideanSpace ℝ (Fin m) → ℝ,
      ConvexOn ℝ {x | ∀ i, 0 ≤ x i} π ∧
      (∀ x y, (∀ i, 0 ≤ x i) → (∀ i, x i ≤ y i) → π x ≤ π y) ∧
      ((∀ r, L r = π (WithLp.toLp 2 (fun i => |r i|))) ∨
       (∀ r, L r = π (WithLp.toLp 2 (fun i => max (r i) 0)))))
    (ψ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hψ0 : ∀ v, 0 ≤ ψ v) (hψz : ∀ v, ψ v = 0 ↔ v = 0)
    (hψh : ∀ (t : ℝ) v, ψ (t • v) = |t| * ψ v)
    (hψa : ∀ v w, ψ (v + w) ≤ ψ v + ψ w)
    (r : EuclideanSpace ℝ (Fin m)) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ M : ℝ,
      IsGreatest (Set.range (fun v : EuclideanSpace ℝ (Fin m) =>
        ((⟪r, v⟫ + κ * ψ v : ℝ) : EReal) - fenchelConjugate L v)) (M : EReal) ∧
      IsGreatest ((fun ξ : EuclideanSpace ℝ (Fin m) => L (r + κ • ξ)) ''
        {ξ | ∀ v : EuclideanSpace ℝ (Fin m), (⟪ξ, v⟫ : ℝ) ≤ ψ v}) M := by sorry

end RobustOpt2009.RobustLoss
