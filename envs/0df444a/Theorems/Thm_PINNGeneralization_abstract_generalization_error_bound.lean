-- Prove2me | Theorems.Thm_PINNGeneralization_abstract_generalization_error_bound
-- name    : PINNGeneralization.abstract_generalization_error_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:45:56.855632+00:00
-- url     : https://prove2.me/theorems/53b15545-52b0-46ae-acb0-c8e5b67ebd46
-- title:
--   Theorem 2.6: abstract estimate on the generalization error of PINNs
-- statement:
--   Let $\mathcal D(u)=f$ be an abstract PDE as in Section 2.1: $\mathbb D\subseteq\mathbb R^{\bar d}$ is measurable, $Y=L^p(\mathbb D;\mathbb R^m)$ with $1\le p<\infty$, $X$ is a separable Banach space, $\mathcal D:X^*\to Y^*$ satisfies (H1)-(H2), and $\mathcal D(v)=g$ has a unique solution $v\in X^*$ for every $g\in Y^*$. Let $Z\subseteq X^*$ be a closed subspace with norm $\|\cdot\|_Z$, and assume the stability bound (H3)
--
--   $$\|v-w\|_X\le C_{pde}(\|v\|_Z,\|w\|_Z)\,\|\mathcal D(v)-\mathcal D(w)\|_Y\qquad(v,w\in Z),$$
--
--   with $C_{pde}>0$. Let $u\in Z$ solve the PDE and let $u^*\in Z$. Let $y_1,\dots,y_N\in\mathbb D$, $N\ge1$, be quadrature points with weights $w_n\ge0$. Let $Z^*$ be a space of real functions on $\mathbb D$ with a norm $\|\cdot\|_{Z^*}$ such that every $g\in Z^*$ is integrable on $\mathbb D$ and
--
--   $$\Big|\int_{\mathbb D}g\,dy-\sum_{n=1}^Nw_ng(y_n)\Big|\le C_{quad}(\|g\|_{Z^*})\,N^{-\alpha},\qquad\alpha>0.$$
--
--   Suppose that $|\mathcal R|^p\in Z^*$, where $\mathcal R=\mathcal D(u^*)-f$. Then, with $\mathcal E_T=\big(\sum_nw_n|\mathcal R(y_n)|^p\big)^{1/p}$,
--
--   $$\|u-u^*\|_X\le C_{pde}\,\mathcal E_T+C_{pde}\,C_{quad}^{1/p}\,N^{-\alpha/p},$$
--
--   where $C_{pde}=C_{pde}(\|u\|_Z,\|u^*\|_Z)$ and $C_{quad}=C_{quad}(\||\mathcal R|^p\|_{Z^*})$.
--
--   This is the paper's central estimate: the error of a PINN is controlled by its training error, the quadrature error and the stability of the PDE.
--
--   **Formalization Note** The PINN $u^*$ is any element of $Z$. As Remark 2.9 notes, the estimate uses neither the network structure nor the training. The paper assumes $\mathcal R\in Z^*$, but its constant $C_{quad}(\||\mathcal R|^p\|)$ and its proof apply the quadrature bound to $|\mathcal R|^p$. The hypothesis is therefore $|\mathcal R|^p\in Z^*$, with $Z^*$ a space of scalar functions.
-- source:
--   Mishra and Molinaro, Estimates on the generalization error of Physics Informed Neural Networks (PINNs) for approximating PDEs, arXiv:2006.16144v3 (2023), Section 2.4, Theorem 2.6, eq. (2.22), p. 8; setting in Sections 2.1-2.2, eqs. (2.1)-(2.3), (2.6)-(2.7), (2.12), (2.20)-(2.21), pp. 3-7

import Mathlib
import Definitions.Def_PINNGeneralization_Basic

open MeasureTheory

namespace PINNGeneralization

theorem abstract_generalization_error_bound {n m : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    (P : AbstractPDE n m X) (hP : P.Hyp)
    (Z : Submodule ℝ X) (zNorm : X → ℝ) (Cpde : ℝ → ℝ → ℝ) (hstab : P.IsStable Z zNorm Cpde)
    (u : X) (hu : P.IsSolution u) (huZ : u ∈ Z) (ustar : X) (hustar : ustar ∈ Z)
    (Zs : Submodule ℝ (Pt n → ℝ)) (zsNorm : (Pt n → ℝ) → ℝ) (hZs : IsNormOn Zs zsNorm)
    (Cquad : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (Q : QuadRule (Pt n)) (hQ : Q.IsOn P.dom) (hN : 0 < Q.N)
    (hquad : QuadErrorBound volume P.dom (Zs : Set (Pt n → ℝ)) zsNorm Cquad α Q)
    (hR : (fun y => ‖P.residual ustar y‖ ^ P.p) ∈ Zs) :
    ‖u - ustar‖ ≤ Cpde (zNorm u) (zNorm ustar) * trainingError Q P.p (P.residual ustar) +
      Cpde (zNorm u) (zNorm ustar) *
        Cquad (zsNorm fun y => ‖P.residual ustar y‖ ^ P.p) ^ (1 / P.p) *
          (Q.N : ℝ) ^ (-α / P.p) := by sorry

end PINNGeneralization
