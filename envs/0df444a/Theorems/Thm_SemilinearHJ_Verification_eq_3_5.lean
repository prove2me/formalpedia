-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_eq_3_5
-- name    : SemilinearHJ.Verification.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:57.457182+00:00
-- url     : https://prove2.me/theorems/5ca77a92-cfd5-441d-8582-a2cdb062a887
-- title:
--   Equation (3.5), p. 8 — linear lower bound H(x, u) ≥ (r/n)|u| − r‖Ψ‖∞
-- statement:
--   Let $X\subset\mathbb R^n$ be a polytope with tangent space $TX$, let $\Psi:X\to\mathbb R^n_+$ be Lipschitz continuous and $r>0$. Let $H(x,u)=\max_{v\in TX\cap B_r}\big(\langle u,v\rangle-\langle\Psi(x),[v]_+\rangle\big)$ be the maximized Hamiltonian (3.4), $|\cdot|$ the $\ell^1$ norm and $\|\Psi\|_\infty=\max_{x\in X}|\Psi(x)|$. Then for every $x\in X$ and every $u\in TX$,
--   $$H(x,u)\ \ge\ \frac rn\,|u|-r\|\Psi\|_\infty .$$
--
--   This coercivity bound is what makes subsolutions of the Hamilton–Jacobi system Lipschitz (Equation (4.7)) and drives the Lipschitz estimate in the proof of Theorem 3.2.
--
--   **Formalization Note** $H$ is defined for every $u\in\mathbb R^n$ but depends only on the $TX$-component of $u$; the paper's $u\in\mathbb R^m$ is a vector of $TX$, which is what the statement quantifies over.
--
--   Differences from the source:
--   - reading: $u\in\mathbb R^m$ with $m=\dim X$ → $u\in TX$ (`vectorSpan ℝ X`); reason: the paper identifies $\mathbb R^m$ with $TX$ (p. 4); for $u\perp TX$ the bound is false when $m<n$, since then $H(x,u)=0$.
--   - encoding: $\Psi:X\to\mathbb R^n_+$ → $\Psi:\mathbb R^n\to\mathbb R^n$, nonnegative and Lipschitz on $X$; reason: values off $X$ are never used.
--   - encoding: $\max$ in (3.4) and in $\|\Psi\|_\infty$ → real `sSup` of the image of a compact nonempty set under a continuous function; reason: the supremum is attained, so it is the maximum.
--   - reading: (3.4) maximizes $\mathcal H(x,u,v)=\langle u,v\rangle-L(x,v)$ over $v\in TX\cap B_r$, which (3.3) equates with $\langle u,v\rangle-\langle\Psi(x),[v]_+\rangle$ → $H$ is the maximum of $\langle u,v\rangle-\langle\Psi(x),[v]_+\rangle$ over all $v\in TX\cap B_r$ (not only $v\in TX(x)$), and the bound is stated for every $x\in X$; reason: the two forms agree on $X^\circ$; at a boundary point they differ, and with $L=+\infty$ off $TX(x)$ the bound fails at a vertex ($X=[0,1]$, $x=0$, $\Psi\equiv1$, $r=1$, $u=-10$: $H=0<9$), so the formula reading is the one under which (3.5) holds on $X$ as printed.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), p. 8, Equation (3.5)

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem eq_3_5 {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ X, ∀ u ∈ vectorSpan ℝ X, r / n * l1 u - r * psiNorm X Ψ ≤ ham X Ψ r x u := by sorry

end SemilinearHJ.Verification
