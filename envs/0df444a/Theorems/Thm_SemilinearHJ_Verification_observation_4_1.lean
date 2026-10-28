-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_observation_4_1
-- name    : SemilinearHJ.Verification.observation_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:59.450154+00:00
-- url     : https://prove2.me/theorems/047b36db-965c-4303-b2b1-f9080d5d61bc
-- title:
--   Observation 4.1, p. 12 — dynamic programming principle V(x) = min over y ∈ B_ρ(x) ∩ X of V(y) + C(y, x)
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$ the speed bound of the running cost (3.1), and $X_0\subseteq X$ compact. Let $V$ be the value function of the source problem (SP) and $C(y,x)$ the minimum cost of travelling from $y$ to $x$, both with values in $[0,+\infty]$. For $x\in X$ and $\rho>0$ let $B_\rho(x)=\{y:\ |y-x|\le\rho\}$ be the closed $\ell^1$ ball of radius $\rho$ around $x$. Then for every $x\in X$ and every $\rho>0$,
--   $$V(x)=\min_{y\in B_\rho(x)\cap X}\big(V(y)+C(y,x)\big),$$
--   that is, $V(x)\le V(y)+C(y,x)$ for every $y\in B_\rho(x)\cap X$, with equality for some such $y$.
--
--   This dynamic programming principle is the tool used to prove that $V$ is a viscosity subsolution (Proposition 4.3).
--
--   **Formalization Note** The radius is called $\rho$ to keep it apart from the speed bound $r$; the statement holds for every $\rho>0$, so it covers the paper's reuse of the letter $r$.
--
--   Differences from the source:
--   - reading: "$B_r(x)$, the closed unit ball in $X$ with center $x$", for $r>0$ → $\{y\in X:\ |y-x|_1\le\rho\}$ for every $\rho>0$; reason: the paper's norm $|\cdot|$ is $\ell^1$ (p. 5) and the radius is the quantified $r>0$; the letter is renamed to avoid a clash with the speed bound $r$, and every radius is covered.
--   - encoding: $\min$ → existence of a minimizer together with the lower bound for every $y$; reason: that is what a minimum means.
--   - encoding: $V$, $C$ real or $+\infty$ → values in `ℝ≥0∞`; reason: $c$ is $+\infty$ for paths faster than $r$ under (3.1), and $\inf\emptyset=+\infty$.
--   - encoding: $\Psi:X\to\mathbb R^n_+$ → $\Psi:\mathbb R^n\to\mathbb R^n$, nonnegative and Lipschitz on $X$; reason: values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 12, Observation 4.1, Equation (4.2)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem observation_4_1 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) :
    ∀ x ∈ X, ∀ ρ : ℝ, 0 < ρ →
      (∃ y ∈ X, l1 (y - x) ≤ ρ ∧ srcVal X Ψ r X0 x = srcVal X Ψ r X0 y + minCost X Ψ r y x) ∧
      ∀ y ∈ X, l1 (y - x) ≤ ρ → srcVal X Ψ r X0 x ≤ srcVal X Ψ r X0 y + minCost X Ψ r y x := by sorry

end SemilinearHJ.Verification
