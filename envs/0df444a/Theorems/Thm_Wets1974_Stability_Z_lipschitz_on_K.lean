-- Prove2me | Theorems.Thm_Wets1974_Stability_Z_lipschitz_on_K
-- name    : Wets1974.Stability.Z_lipschitz_on_K
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T14:36:27.806985+00:00
-- url     : https://prove2.me/theorems/3d62fb12-dd66-435f-915b-bdcab483c0bc
-- title:
--   Theorem 7.7 — if $Z$ is bounded on $K$, then $Z$ is Lipschitz on $K$
-- statement:
--   Consider a stochastic program with fixed recourse whose random element $\xi$, with law a probability measure $\mu$, satisfies the weak covariance condition (Definition 2.2), and whose recourse matrix $W$ has full row rank (the paper's standing assumption, p. 312). Let $Z(x)=\bar cx+\mathcal Q(x)$ and $K=K_1\cap K_2$ be as in the model. Suppose $Z$ is bounded on $K$, i.e. $Z(x)>-\infty$ for every $x\in K$. Then $Z$ is finite on $K$ and satisfies a Lipschitz condition there: there is a constant $\bar B$ such that
--   $$|Z(x)-Z(x^0)|\le\bar B\,\|x-x^0\|\qquad\text{for all }x,x^0\in K,$$
--   where $\|\cdot\|$ is the Euclidean norm of $\mathbb R^n$.
--
--   Together with Theorem 7.6 this shows that, whenever the deterministic equivalent program is not identically $-\infty$, its objective is a finite, convex, Lipschitz function on the feasible region; this is the regularity used for the stability result, Theorem 8.11.
--
--   **Formalization Note** The paper writes "$Z(x)$ is bounded on $K$". By Theorem 7.6, $Z$ is either finite or identically $-\infty$ on $K$, and the proof opens with "if $\mathcal Q(x)>-\infty$ on $K_2$"; the hypothesis is therefore read as $Z>-\infty$ on $K$, which is weaker than a two-sided bound $|Z|\le M$ and makes the theorem stronger. Finiteness on $K$ is part of the conclusion, so that `toReal` is exact. The constant $\bar B$ may depend on the instance. The Euclidean norm is written as $\sqrt{\sum_i (x_i-x^0_i)^2}$.
-- source:
--   Wets, Stochastic Programs with Fixed Recourse: The Equivalent Deterministic Program, SIAM Review 16(3), 1974, pp. 329-330, Theorem 7.7

import Mathlib
import Definitions.Def_Wets1974_Stability_Model

namespace Wets1974.Stability

open MeasureTheory Matrix

/-- Theorem 7.7, pp. 329–330: under the weak covariance condition (and the standing full row
rank of `W`, p. 312), if `Z` is bounded (i.e. `> −∞`) on `K`, then `Z` is finite on `K` and
Lipschitz there for the Euclidean norm: `|Z(x) − Z(x⁰)| ≤ B̄ ‖x − x⁰‖` for `x, x⁰ ∈ K`. -/
theorem Z_lipschitz_on_K {n nb mb m : ℕ} (μ : Measure (DataSpace n nb mb))
    [IsProbabilityMeasure μ] (hcov : WeakCovariance μ)
    (W : Matrix (Fin mb) (Fin nb) ℝ) (hW : FullRowRank W)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hbdd : ∀ x ∈ K μ W A b, Z μ W x ≠ ⊥) :
    (∀ x ∈ K μ W A b, Z μ W x ≠ ⊥ ∧ Z μ W x ≠ ⊤) ∧
      ∃ Bbar : ℝ, ∀ x ∈ K μ W A b, ∀ x₀ ∈ K μ W A b,
        |(Z μ W x).toReal - (Z μ W x₀).toReal| ≤
          Bbar * Real.sqrt (∑ i, (x i - x₀ i) ^ 2) := by sorry

end Wets1974.Stability
