-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_theorem_4_2
-- name    : SemilinearHJ.Verification.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:15.220999+00:00
-- url     : https://prove2.me/theorems/a4da298f-5253-4b43-99cf-7756f1b884e0
-- title:
--   Theorem 4.2, p. 12 — the value function of (SP) is the unique maximal viscosity solution of (4.1) (corrected: X0 nonempty)
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope, $\Psi:X\to\mathbb R^n_+$ Lipschitz continuous, $r>0$, and $X_0\subseteq X$ compact and nonempty. Let $V$ be the value function of the source problem (SP). Then $V$ is finite on $X$, $V$ is a maximal viscosity solution of the state-constrained system
--   $$H(x,DV(x))\le 0\ \text{in } X^\circ,\qquad H(x,DV(x))\ge0\ \text{on } X,\qquad V(x^*)=0\ \text{for all } x^*\in X_0$$
--   (Definitions 1–2), and it is the only one: every maximal viscosity solution $V'$ of (4.1) coincides with $V$ on $X$.
--
--   The system (4.1) has many viscosity solutions (for instance $V\equiv0$); this theorem singles out the value function as the largest one, and is the bridge from optimal control to the almost-everywhere characterization of Theorem 3.2.
--
--   Differences from the source:
--   - correction: $X_0$ any compact subset of $X$ → $X_0$ nonempty; reason: for $X_0=\emptyset$, $V\equiv+\infty$ is not in $C(X)$ and every constant is a viscosity solution, so no maximal one exists (counterexample: $n=m=1$, $X=[0,1]$, $\Psi\equiv1$, $r=1$, $X_0=\emptyset$).
--   - encoding: $V:X\to\mathbb R$ → $V(x)\neq+\infty$ for all $x\in X$, and the property for the real function `(V x).toReal`; reason: the value function is computed in $[0,+\infty]$.
--   - encoding: "the unique maximal solution" → $V$ is maximal and every maximal viscosity solution equals $V$ on $X$; reason: functions on $X$ are compared on $X$ only.
--   - reading: "$V-\varphi$ has a maximum (minimum) at $x_0$" in Definition 1 → a local maximum (minimum) relative to $X$; reason: the standard viscosity notion (Crandall–Evans–Lions 1984) cited by the paper.
--   - encoding: $\varphi\in C^\infty(X)$ → $\varphi$ smooth on $\mathbb R^n$, $D\varphi(x_0)$ → its gradient; reason: smooth functions near $X$ extend, and $H$ only sees the $TX$-component.
--   - encoding: $\Psi:X\to\mathbb R^n_+$ → $\Psi:\mathbb R^n\to\mathbb R^n$, nonnegative and Lipschitz on $X$; reason: values off $X$ are never used.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 12, Theorem 4.2

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem theorem_4_2 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      IsMaxViscSol X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) ∧
      ∀ V' : E n → ℝ, IsMaxViscSol X Ψ r X0 V' →
        ∀ x ∈ X, V' x = (srcVal X Ψ r X0 x).toReal := by sorry

end SemilinearHJ.Verification
