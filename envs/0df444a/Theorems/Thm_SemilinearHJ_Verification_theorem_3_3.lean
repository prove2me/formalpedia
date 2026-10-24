-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_theorem_3_3
-- name    : SemilinearHJ.Verification.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:33.422134+00:00
-- url     : https://prove2.me/theorems/43b48933-b151-4255-ba76-570e17207b1d
-- title:
--   Theorem 3.3, p. 9 — the value function of (TP) is the maximal Lipschitz a.e. subsolution of (3.10) (corrected: Y nonempty)
-- statement:
--   Let $X\subset\mathbb R^n$ be an $m$-dimensional polytope with relative interior $X^\circ$, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $Y\subseteq X$ compact and nonempty. Let $W$ be the value function of the target problem (TP) under the running cost (3.1). Then $W$ is finite on $X$ and is the maximal Lipschitz continuous function $W:X\to\mathbb R$ satisfying
--   $$\begin{cases}H(x,-DW(x))\le0 & \text{for almost all } x\in X^\circ,\\ W(y^*)=0&\text{for all } y^*\in Y.\end{cases}\tag{3.10}$$
--   That is: $W$ is Lipschitz on $X$ and satisfies (3.10), and every Lipschitz $W':X\to\mathbb R$ satisfying (3.10) has $W'\le W$ on $X$. "Almost all" refers to $m$-dimensional Hausdorff measure on $X^\circ$, and $DW(x)$ is the derivative relative to $X$, identified with a vector of $TX$.
--
--   This is the characterization of the target problem, the counterpart of Theorem 3.2 under time reversal; the verification theorem (Theorem 3.4) is deduced from it.
--
--   Differences from the source:
--   - correction: $Y$ any compact subset of $X$ → $Y$ nonempty; reason: for $Y=\emptyset$, $W\equiv+\infty$ is not a function $X\to\mathbb R$ and every constant satisfies (3.10) since $H(x,0)=0$, so no maximal function exists (counterexample: $n=m=1$, $X=[0,1]$, $\Psi\equiv1$, $r=1$, $Y=\emptyset$).
--   - encoding: $W:X\to\mathbb R$ → $W(x)\neq+\infty$ for all $x\in X$, and all other clauses for the real function `(W x).toReal`; reason: the value function is computed in $[0,+\infty]$.
--   - encoding: "$H(x,-DW(x))\le0$ for almost all $x\in X^\circ$" → for $\mu^m$-almost every $x\in X^\circ$ there is $w\in TX$ with $W$ differentiable at $x$ relative to $X$ with derivative $\langle w,\cdot\rangle$ and $H(x,-w)\le0$; reason: Lebesgue measure on $\mathbb R^n$ would make the condition vacuous when $m<n$; a Lipschitz function is differentiable almost everywhere.
--   - encoding: Lipschitz $W':X\to\mathbb R$ → $W':\mathbb R^n\to\mathbb R$ Lipschitz on $X$, compared on $X$; $\Psi$ likewise; reason: values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 9, Theorem 3.3, Equation (3.10)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem theorem_3_3 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (Y : Set (E n)) (hYc : IsCompact Y) (hYX : Y ⊆ X) (hY : Y.Nonempty) :
    (∀ x ∈ X, tgtVal X Ψ r Y x ≠ ⊤) ∧
      (∃ K : NNReal, LipschitzOnWith K (fun x => (tgtVal X Ψ r Y x).toReal) X) ∧
      AESubsolNeg X Ψ r (fun x => (tgtVal X Ψ r Y x).toReal) ∧
      (∀ y ∈ Y, (tgtVal X Ψ r Y y).toReal = 0) ∧
      ∀ W' : E n → ℝ, (∃ K : NNReal, LipschitzOnWith K W' X) → AESubsolNeg X Ψ r W' →
        (∀ y ∈ Y, W' y = 0) → ∀ x ∈ X, W' x ≤ (tgtVal X Ψ r Y x).toReal := by sorry

end SemilinearHJ.Verification
