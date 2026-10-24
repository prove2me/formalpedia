-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_theorem_3_4
-- name    : SemilinearHJ.Verification.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:15.374995+00:00
-- url     : https://prove2.me/theorems/c0a12879-25d6-429f-9e68-43f59afa8eec
-- title:
--   Theorem 3.4, p. 9 — verification: a Lipschitz a.e. subsolution of (3.10), zero on Y and attained by paths, is the value function of (TP)
-- statement:
--   Let $X\subset\mathbb R^n$ be an $m$-dimensional polytope with relative interior $X^\circ$, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $Y\subseteq X$ compact. Consider the running cost (3.1), the path cost $c(\phi)=\int_0^TL(\phi(t),\dot\phi(t))\,dt$ of a Lipschitz path $\phi\in\Phi_T$ in $X$, and the target problem
--   $$W^{\mathrm{TP}}(x)=\inf\{c(\phi):\ \phi\in\Phi_T\text{ for some }T\ge0,\ \phi(0)=x,\ \phi(T)\in Y\}.$$
--   Suppose that $W:X\to\mathbb R$ is Lipschitz continuous with $W(y^*)=0$ for all $y^*\in Y$. Suppose in addition that for each $x\in X\setminus Y$ there are a time $T>0$ and a path $\phi\in\Phi_T$ with $\phi(0)=x$ and $\phi(T)\in Y$ such that $W(x)=c(\phi)$. If $W$ satisfies
--   $$H(x,-DW(x))\le0\qquad\text{for almost all }x\in X^\circ,\tag{3.10}$$
--   then $W$ is the solution to (TP): $W^{\mathrm{TP}}(x)=W(x)$ for every $x\in X$.
--
--   This verification theorem replaces the maximality requirement of Theorem 3.3 by attainability: exhibiting a candidate function together with paths achieving its values certifies optimality, including when the state constraint binds. It is the tool the paper uses to solve exit and transition problems in evolutionary game theory.
--
--   Differences from the source:
--   - encoding: $W(x)=c(\phi)$ → $c(\phi)<+\infty$ and its real value equals $W(x)$; reason: path costs live in $[0,+\infty]$; writing $c(\phi)=\max(W(x),0)$ instead would admit $W(x)<0$.
--   - encoding: "$W$ is the solution to (TP)" → for every $x\in X$ the value of (TP) is finite and equals $W(x)$; reason: the value function is computed in $[0,+\infty]$.
--   - encoding: "$H(x,-DW(x))\le0$ for almost all $x\in X^\circ$" → for $\mu^m$-almost every $x\in X^\circ$ ($m$-dimensional Hausdorff measure) there is $w\in TX$ with $W$ differentiable at $x$ relative to $X$ with derivative $\langle w,\cdot\rangle$ and $H(x,-w)\le0$; reason: Lebesgue measure on $\mathbb R^n$ would make the hypothesis vacuous when $m<n$; a Lipschitz function is differentiable almost everywhere.
--   - encoding: $W:X\to\mathbb R$, $\Psi:X\to\mathbb R^n_+$, $\phi:[0,T]\to X$ → functions on $\mathbb R^n$ (resp. $\mathbb R$) constrained only on $X$ (resp. $[0,T]$), with $\dot\phi$ the derivative within $[0,T]$; reason: Lean functions are total and the other values are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 9, Theorem 3.4

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem theorem_3_4 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (Y : Set (E n)) (hYc : IsCompact Y) (hYX : Y ⊆ X)
    (W : E n → ℝ) (hWL : ∃ K : NNReal, LipschitzOnWith K W X) (hWY : ∀ y ∈ Y, W y = 0)
    (hatt : ∀ x ∈ X \ Y, ∃ T : ℝ, 0 < T ∧ ∃ φ : ℝ → E n, IsPath X T φ ∧ φ 0 = x ∧ φ T ∈ Y ∧
      pathCost X Ψ r T φ ≠ ⊤ ∧ (pathCost X Ψ r T φ).toReal = W x)
    (hsub : AESubsolNeg X Ψ r W) :
    ∀ x ∈ X, tgtVal X Ψ r Y x ≠ ⊤ ∧ (tgtVal X Ψ r Y x).toReal = W x := by sorry

end SemilinearHJ.Verification
