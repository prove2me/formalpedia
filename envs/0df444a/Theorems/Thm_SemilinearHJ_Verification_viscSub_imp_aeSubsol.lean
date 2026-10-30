-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_viscSub_imp_aeSubsol
-- name    : SemilinearHJ.Verification.viscSub_imp_aeSubsol
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T10:36:54.127467+00:00
-- url     : https://prove2.me/theorems/24822d51-d3dc-442e-97e0-15b8e5e52b73
-- title:
--   Proof of Theorem 3.2, p. 16: a Lipschitz viscosity subsolution of (4.1) satisfies $H(x,DV(x))\le 0$ a.e. in $X^\circ$
-- statement:
--   Let $X\subset\mathbb R^n$ be an $m$-dimensional polytope with relative interior $X^\circ$, let $\Psi:X\to\mathbb R^n_+$ be Lipschitz continuous, let $r>0$, and let $X_0\subseteq X$ be compact. Let $H$ be the maximized Hamiltonian (3.4),
--   $$H(x,u)=\max_{v\in TX\cap B_r}\Big(\langle u,v\rangle-\langle\Psi(x),[v]_+\rangle\Big).$$
--   If $V:X\to\mathbb R$ is Lipschitz continuous and is a viscosity subsolution of (4.1) in the sense of Definition 1, then $V$ satisfies the first line of (3.9):
--   $$H(x,DV(x))\le0\qquad\text{for almost every }x\in X^\circ.$$
--   Here "almost every" refers to $m$-dimensional Hausdorff measure on $X^\circ$, and $DV(x)$ is the derivative of $V$ relative to $X$, identified with a vector of $TX$. Being a viscosity subsolution includes $V=0$ on $X_0$.
--
--   This is the step "In particular, $V$ is differentiable almost everywhere in $X^\circ$ and satisfies (3.9)" in the proof of Theorem 3.2 (p. 16). It combines Rademacher's theorem on the affine hull of $X$ with the fact that a viscosity subsolution satisfies the equation classically at every point of differentiability. Together with Theorem 4.2, equation (4.7) and the converse statement `aeSubsol_imp_viscSub`, it yields Theorem 3.2.
--
--   **Formalization Note** "$H(x,DV(x))\le0$ a.e." is encoded by `AESubsol`: for $\mu^m$-a.e. $x\in X^\circ$ there is $w\in TX$ with $V$ having derivative $\langle w,\cdot\rangle$ at $x$ relative to $X$ and $H(x,w)\le0$. On $X_0\cap X^\circ$ the conclusion still holds a.e., because there the relative gradient vanishes at a.e. point and $H(x,0)=0$. Functions are defined on all of $\mathbb R^n$, and only their values on $X$ matter.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), https://people.math.wisc.edu/~htran24/hjld.pdf, p. 16, Section 4.2, proof of Theorem 3.2

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem viscSub_imp_aeSubsol {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X)
    (V : E n → ℝ) (hVL : ∃ K : NNReal, LipschitzOnWith K V X) (hV : IsViscSub X Ψ r X0 V) :
    AESubsol X Ψ r V := by sorry

end SemilinearHJ.Verification
