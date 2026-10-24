-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_eq_4_7
-- name    : SemilinearHJ.Verification.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:00.396683+00:00
-- url     : https://prove2.me/theorems/9b4bd796-7c59-426e-93c1-16200cb711d7
-- title:
--   Equation (4.7), p. 13 — every viscosity solution V̂ of (4.1) is Lipschitz with ‖DV̂‖∞ ≤ n‖Ψ‖∞
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope with relative interior $X^\circ$ and dimension $m$, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $X_0\subseteq X$ compact. Let $\hat V$ be any viscosity solution of the system (4.1) in the sense of Definition 1. Then $\hat V$ is Lipschitz continuous on $X$ and
--   $$\|D\hat V\|_\infty\le n\,\|\Psi\|_\infty ,$$
--   where $D\hat V(x)$ is identified with the vector $w\in TX$ representing it, $|w|$ is the $\ell^1$ norm, $\|\Psi\|_\infty=\max_{x\in X}|\Psi(x)|$, and the $L^\infty$ norm is taken over $X^\circ$: for almost every $x\in X^\circ$, every relative gradient $w$ of $\hat V$ at $x$ satisfies $|w|\le n\|\Psi\|_\infty$.
--
--   The bound is claimed in the proof of Proposition 4.4 as a consequence of the coercivity bound (3.5) and proved in Appendix A; it is what allows Rademacher's theorem and mollification to be applied to arbitrary viscosity solutions.
--
--   Differences from the source:
--   - encoding: $\|D\hat V\|_\infty\le n\|\Psi\|_\infty$ → for almost every $x\in X^\circ$ (w.r.t. $m$-dimensional Hausdorff measure), every $w\in TX$ with $\hat V$ differentiable at $x$ relative to $X$ with derivative $\langle w,\cdot\rangle$ has $|w|_1\le n\|\Psi\|_\infty$; reason: the essential supremum of the $\ell^1$ norm of the gradient over $X^\circ$, with $D\hat V(x)$ identified with $w\in TX$ as on p. 13; a Lipschitz function is differentiable almost everywhere.
--   - reading: "$\hat V-\varphi$ has a maximum (minimum) at $x_0$" in Definition 1 → a local maximum (minimum) relative to $X$; reason: the standard viscosity notion (Crandall–Evans–Lions 1984) cited by the paper.
--   - encoding: $\varphi\in C^\infty(X)$ → $\varphi$ smooth on $\mathbb R^n$, $D\varphi(x_0)$ → its gradient; reason: smooth functions near $X$ extend, and $H$ only sees the $TX$-component.
--   - encoding: $\hat V, \Psi$ functions on $X$ → functions on $\mathbb R^n$ whose values off $X$ are never used; reason: Lean functions are total.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 13, Equation (4.7) (proof of Proposition 4.4; derived in Appendix A, pp. 34–35)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem eq_4_7 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) :
    ∀ Vh : E n → ℝ, IsViscSol X Ψ r X0 Vh →
      (∃ K : NNReal, LipschitzOnWith K Vh X) ∧
      ∀ᵐ x ∂(interiorMeasure X), ∀ w, relGrad X Vh x w → l1 w ≤ n * psiNorm X Ψ := by sorry

end SemilinearHJ.Verification
