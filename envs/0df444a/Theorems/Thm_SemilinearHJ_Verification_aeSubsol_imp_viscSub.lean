-- Prove2me | Theorems.Thm_SemilinearHJ_Verification_aeSubsol_imp_viscSub
-- name    : SemilinearHJ.Verification.aeSubsol_imp_viscSub
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T10:37:00.203249+00:00
-- url     : https://prove2.me/theorems/a8a1002d-d0f7-4726-98f4-eea2218cfeaa
-- title:
--   Proof of Theorem 3.2, p. 16: a Lipschitz a.e. subsolution of (3.9) is a viscosity subsolution of (4.1)
-- statement:
--   Let $X\subset\mathbb R^n$ be an $m$-dimensional polytope with relative interior $X^\circ$, let $\Psi:X\to\mathbb R^n_+$ be Lipschitz continuous, let $r>0$, and let $X_0\subseteq X$ be compact. Let $H$ be the maximized Hamiltonian (3.4). Let $\hat V:X\to\mathbb R$ be Lipschitz continuous with $\hat V(x^*)=0$ for all $x^*\in X_0$, and suppose
--   $$H(x,D\hat V(x))\le0\qquad\text{for almost every }x\in X^\circ,$$
--   with "almost every" taken for $m$-dimensional Hausdorff measure. Then $\hat V$ is a viscosity subsolution of (4.1) in the sense of Definition 1. That is, for every $C^\infty$ test function $\varphi$ such that $\hat V-\varphi$ has a local maximum relative to $X$ at a point $x_0\in X^\circ\setminus X_0$,
--   $$H(x_0,D\varphi(x_0))\le0.$$
--
--   This is the step in the proof of Theorem 3.2 (p. 16) where an arbitrary Lipschitz solution $\hat V$ of (3.9) is mollified, $V^\varepsilon=\rho_\varepsilon*\hat V$, which satisfies $H(x,DV^\varepsilon(x))\le K\varepsilon$ classically on $X_r$, and the stability of viscosity subsolutions then gives that $\hat V$ is a viscosity subsolution on $X^\circ=\bigcup_{r>0}X_r$. It is the convexity of $H(x,\cdot)$ that makes almost-everywhere subsolutions viscosity subsolutions.
--
--   **Formalization Note** The hypothesis is `AESubsol` (the first line of (3.9), as in Theorem 3.2), and the conclusion is `IsViscSub`. Test functions are smooth on $\mathbb R^n$, $D\varphi(x_0)$ is their gradient, and maxima are local relative to $X$, as in the platform's Definition 1. Functions are defined on all of $\mathbb R^n$, and only their values on $X$ matter.
-- source:
--   Sandholm, Tran & Arigapudi, Hamilton-Jacobi Equations with Semilinear Costs and State Constraints, with Applications to Large Deviations in Games, author's manuscript (July 4, 2018; Math. Oper. Res. doi:10.1287/moor.2020.1114), https://people.math.wisc.edu/~htran24/hjld.pdf, p. 16, Section 4.2, proof of Theorem 3.2

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting

namespace SemilinearHJ.Verification

open scoped ENNReal MeasureTheory

theorem aeSubsol_imp_viscSub {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X)
    (V : E n → ℝ) (hVL : ∃ K : NNReal, LipschitzOnWith K V X) (hV : AESubsol X Ψ r V)
    (hV0 : ∀ x ∈ X0, V x = 0) :
    IsViscSub X Ψ r X0 V := by sorry

end SemilinearHJ.Verification
