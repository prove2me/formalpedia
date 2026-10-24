-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_eq_4_11
-- name    : SemilinearHJ.Verification.eq_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:00.16876+00:00
-- url     : https://prove2.me/theorems/04b7b2d1-305d-4efa-b6a3-64fefe4728f1
-- title:
--   Equation (4.11), p. 15 — every viscosity solution satisfies V̂(x) ≤ V̂(y) + C(y, x) for x, y ∈ X°
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope with relative interior $X^\circ$, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $X_0\subseteq X$ compact. Let $\hat V$ be any viscosity solution of the system (4.1) in the sense of Definition 1, and let $C(y,x)\in[0,+\infty]$ be the minimum cost of travelling from $y$ to $x$ along Lipschitz paths in $X$. Then for all $x,y\in X^\circ$,
--   $$\hat V(x)\le\hat V(y)+C(y,x).$$
--
--   This comparison of an arbitrary viscosity solution with travel costs is the core of the maximality part of Proposition 4.4: letting $y$ tend to $X_0$ gives $\hat V\le V$.
--
--   Differences from the source:
--   - encoding: $\hat V(x)\le\hat V(y)+C(y,x)$ → $\max(\hat V(x)-\hat V(y),0)\le C(y,x)$ in $[0,+\infty]$; reason: equivalent because $C\ge 0$, and it covers $C(y,x)=+\infty$ without mixing real and extended values.
--   - reading: "$\hat V-\varphi$ has a maximum (minimum) at $x_0$" in Definition 1 → a local maximum (minimum) relative to $X$; reason: the standard viscosity notion (Crandall–Evans–Lions 1984) cited by the paper.
--   - encoding: $\varphi\in C^\infty(X)$ → $\varphi$ smooth on $\mathbb R^n$, $D\varphi(x_0)$ → its gradient; reason: smooth functions near $X$ extend, and $H$ only sees the $TX$-component.
--   - encoding: $\hat V, \Psi$ functions on $X$ → functions on $\mathbb R^n$ whose values off $X$ are never used; reason: Lean functions are total.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), pp. 14–15, Equation (4.11) (proof of Proposition 4.4; x, y ∈ X° fixed on p. 14)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem eq_4_11 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) :
    ∀ Vh : E n → ℝ, IsViscSol X Ψ r X0 Vh →
      ∀ x ∈ intrinsicInterior ℝ X, ∀ y ∈ intrinsicInterior ℝ X,
        ENNReal.ofReal (Vh x - Vh y) ≤ minCost X Ψ r y x := by sorry

end SemilinearHJ.Verification
