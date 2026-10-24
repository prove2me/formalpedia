-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_theorem_3_2
-- name    : SemilinearHJ.Verification.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:03.529125+00:00
-- url     : https://prove2.me/theorems/f4958b9d-5ae3-4278-9fc1-8b27440b0fbf
-- title:
--   Theorem 3.2, p. 9 — the value function of (SP) is the maximal Lipschitz a.e. subsolution of (3.9) (corrected: X0 nonempty)
-- statement:
--   Let $X\subset\mathbb R^n$ be an $m$-dimensional polytope with relative interior $X^\circ$, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $X_0\subseteq X$ compact and nonempty. Let $V$ be the value function of the source problem (SP) under the running cost (3.1). Then $V$ is finite on $X$ and is the maximal Lipschitz continuous function $V:X\to\mathbb R$ satisfying
--   $$\begin{cases}H(x,DV(x))\le0 & \text{for almost all } x\in X^\circ,\\ V(x^*)=0&\text{for all } x^*\in X_0.\end{cases}\tag{3.9}$$
--   That is: $V$ is Lipschitz on $X$ and satisfies (3.9), and every Lipschitz $V':X\to\mathbb R$ satisfying (3.9) has $V'\le V$ on $X$. Here "almost all" refers to $m$-dimensional Hausdorff measure on $X^\circ$, and $DV(x)$ is the derivative of $V$ relative to $X$, identified with a vector of $TX$.
--
--   This is the paper's characterization of the source problem: subsolution inequalities need not be checked at boundary states or at non-differentiability points.
--
--   Differences from the source:
--   - correction: $X_0$ any compact subset of $X$ → $X_0$ nonempty; reason: for $X_0=\emptyset$, $V\equiv+\infty$ is not a function $X\to\mathbb R$ and every constant satisfies (3.9) since $H(x,0)=0$, so no maximal function exists (counterexample: $n=m=1$, $X=[0,1]$, $\Psi\equiv1$, $r=1$, $X_0=\emptyset$).
--   - encoding: $V:X\to\mathbb R$ → $V(x)\neq+\infty$ for all $x\in X$, and all other clauses for the real function `(V x).toReal`; reason: the value function is computed in $[0,+\infty]$.
--   - encoding: "$H(x,DV(x))\le0$ for almost all $x\in X^\circ$" → for $\mu^m$-almost every $x\in X^\circ$ ($\mu^m$ the $m$-dimensional Hausdorff measure, $m=\dim TX$) there is $w\in TX$ with $V$ differentiable at $x$ relative to $X$ with derivative $\langle w,\cdot\rangle$ and $H(x,w)\le0$; reason: Lebesgue measure on $\mathbb R^n$ would make the condition vacuous when $m<n$; a Lipschitz function is differentiable almost everywhere, so asking for the derivative to exist changes nothing.
--   - encoding: Lipschitz $V':X\to\mathbb R$ → $V':\mathbb R^n\to\mathbb R$ Lipschitz on $X$, compared on $X$; $\Psi$ likewise; reason: values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 9, Theorem 3.2, Equation (3.9)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem theorem_3_2 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      (∃ K : NNReal, LipschitzOnWith K (fun x => (srcVal X Ψ r X0 x).toReal) X) ∧
      AESubsol X Ψ r (fun x => (srcVal X Ψ r X0 x).toReal) ∧
      (∀ x ∈ X0, (srcVal X Ψ r X0 x).toReal = 0) ∧
      ∀ V' : E n → ℝ, (∃ K : NNReal, LipschitzOnWith K V' X) → AESubsol X Ψ r V' →
        (∀ x ∈ X0, V' x = 0) → ∀ x ∈ X, V' x ≤ (srcVal X Ψ r X0 x).toReal := by sorry

end SemilinearHJ.Verification
