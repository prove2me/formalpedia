-- Prove2me | Theorems.Thm_Wets1974_Stability_Z_convex_finite_or_bot
-- name    : Wets1974.Stability.Z_convex_finite_or_bot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:35:44.04831+00:00
-- url     : https://prove2.me/theorems/6968cb50-2c26-466c-9555-b151aa6c7fcd
-- title:
--   Theorem 7.6 — $Z(x)=\bar c x+\mathcal Q(x)$ is convex on $K$, and either finite on $K$ or identically $-\infty$
-- statement:
--   Consider a stochastic program with fixed recourse whose random element $\xi=(c,q,p,T)$, with law a probability measure $\mu$, satisfies the weak covariance condition (Definition 2.2). Let $Z(x)=\bar c x+\mathcal Q(x)$ be the objective of the deterministic equivalent program ((3.1), with the paper's integral), and $K=K_1\cap K_2$ its feasible region, where $K_1=\{x: Ax=b,\ x\ge0\}$ and $K_2$ is the induced constraint set of Corollary 4.5. Then one of the following holds (they exclude each other unless $K=\emptyset$):
--
--   1. $Z$ is **finite on $K$** ($-\infty<Z(x)<+\infty$ for every $x\in K$) and **convex on $K$**:
--   $$Z(\lambda x+(1-\lambda)x')\le\lambda Z(x)+(1-\lambda)Z(x')\qquad(x,x'\in K,\ 0\le\lambda\le1),$$
--   which includes the convexity of $K$;
--   2. $Z(x)=-\infty$ for **every** $x\in K$.
--
--   This is the structural fact about the deterministic equivalent program: it is a convex program, and it cannot be finite at some feasible points and $-\infty$ at others.
--
--   **Formalization Note** "Convex" for an extended-real function is folded into the dichotomy: a function identically $-\infty$ is convex, and on the finite branch the statement is `ConvexOn ℝ K (fun x => (Z x).toReal)`, where `toReal` is exact because finiteness is asserted in the same branch. The identity $E\{c(\xi)x+Q(x,\xi)\}=\bar cx+\mathcal Q(x)$ is the paper's definition (3.1) and is built into $Z$. The standing full-rank assumption on $W$ (p. 312) is not needed for this statement and is omitted, which makes it stronger.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, p. 329, Theorem 7.6

import Mathlib
import Definitions.Def_Wets1974_Stability_Model

namespace Wets1974.Stability

open MeasureTheory Matrix

/-- Theorem 7.6, p. 329: under the weak covariance condition, `Z(x) = c̄ x + 𝒬(x)` is either
finite and convex on `K = K₁ ∩ K₂`, or identically `−∞` on `K`. -/
theorem Z_convex_finite_or_bot {n nb mb m : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (hcov : WeakCovariance μ)
    (W : Matrix (Fin mb) (Fin nb) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ((∀ x ∈ K μ W A b, Z μ W x ≠ ⊥ ∧ Z μ W x ≠ ⊤) ∧
        ConvexOn ℝ (K μ W A b) (fun x => (Z μ W x).toReal)) ∨
      ∀ x ∈ K μ W A b, Z μ W x = ⊥ := by sorry

end Wets1974.Stability
