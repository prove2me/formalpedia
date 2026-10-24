-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_proposition_4_3
-- name    : SemilinearHJ.Verification.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:53.475248+00:00
-- url     : https://prove2.me/theorems/f37001d7-e122-4836-bedd-39f55aa04afd
-- title:
--   Proposition 4.3, p. 13 — the value function V of (SP) is a viscosity subsolution of (4.1) (corrected: X0 nonempty)
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $X_0\subseteq X$ compact and nonempty. Let $V$ be the value function of the source problem (SP). Then $V$ is finite on $X$, and the real function $V:X\to\mathbb R$ is a viscosity subsolution of the state-constrained system
--   $$H(x,DV(x))\le 0\ \text{in } X^\circ,\qquad H(x,DV(x))\ge0\ \text{on } X,\qquad V(x^*)=0\ \text{for all } x^*\in X_0,$$
--   in the sense of Definition 1: $V$ is continuous on $X$, vanishes on $X_0$, and $H(x_0,D\varphi(x_0))\le 0$ for every $C^\infty$ test function $\varphi$ such that $V-\varphi$ has a local maximum relative to $X$ at a point $x_0\in X^\circ\setminus X_0$.
--
--   This is the first half of Theorem 4.2: the value function solves (4.1).
--
--   Differences from the source:
--   - correction: $X_0$ any compact subset of $X$ → $X_0$ nonempty; reason: for $X_0=\emptyset$ the value function is $V\equiv+\infty$, which is not in $C(X)$ as Definition 1 requires (counterexample: $n=m=1$, $X=[0,1]$, $\Psi\equiv1$, $r=1$, $X_0=\emptyset$).
--   - encoding: $V:X\to\mathbb R$ → $V(x)\neq+\infty$ for all $x\in X$, and the subsolution property for the real function `(V x).toReal`; reason: the value function is computed in $[0,+\infty]$, and finiteness is asserted before it is read as a real number.
--   - reading: "$V-\varphi$ has a maximum at $x_0$" → a local maximum relative to $X$; reason: the standard viscosity notion of Crandall–Evans–Lions (1984), which the paper cites; the proof (p. 13) only uses a neighbourhood of $x_0$.
--   - encoding: $\varphi\in C^\infty(X)$ → $\varphi$ smooth on $\mathbb R^n$, $D\varphi(x_0)$ → its gradient; reason: smooth functions near $X$ extend to $\mathbb R^n$, and $H$ only sees the $TX$-component of the gradient, which is $D\varphi(x_0)\in L(TX,\mathbb R)$.
--   - encoding: $\Psi:X\to\mathbb R^n_+$ → $\Psi:\mathbb R^n\to\mathbb R^n$, nonnegative and Lipschitz on $X$; reason: values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 13, Proposition 4.3

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem proposition_4_3 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      IsViscSub X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) := by sorry

end SemilinearHJ.Verification
