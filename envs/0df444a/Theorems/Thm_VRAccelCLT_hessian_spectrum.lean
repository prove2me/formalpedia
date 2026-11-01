-- Prove2me | Theorems.Thm_VRAccelCLT_hessian_spectrum
-- name    : VRAccelCLT.hessian_spectrum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:00.98998+00:00
-- url     : https://prove2.me/theorems/dab40dba-8070-4fe2-a8e6-cea679e40b23
-- title:
--   Hessian spectrum at $x^*$ lies in $[\eta, L]$ (proof of Theorem 1)
-- statement:
--   Let $f:\mathbb R^m\to\mathbb R$ satisfy Assumption 1 (i)–(ii) with constants $L,\eta>0$, let $x^*$ be the minimizer of $f$, and let $H\in\mathbb R^{m\times m}$ be the Hessian of $f$ at $x^*$ in the sense of Assumption 2 (i). Then $H$ is symmetric and its eigenvalues $\lambda_1\ge\dots\ge\lambda_m$ satisfy
--
--   $$
--   0<\eta\le\lambda_m\le\lambda_{m-1}\le\cdots\le\lambda_1\le L .
--   $$
--
--   This spectral localization is what makes $\|I_m-\alpha H\|<1$ in Theorem 1 and gives the bound (46) on $\rho(H_2)$ in Theorem 2.
--
--   **Formalization Note** Symmetry is part of the conclusion; the eigenvalues are those of the symmetric matrix $H$. The ordering is a labelling and is not stated.
--
--   Differences from the source:
--   - reading: H has eigenvalues λ1, …, λm with 0 < η ≤ λm ≤ … ≤ λ1 ≤ L → H is symmetric and each of its eigenvalues lies in [η, L]; reason: the paper treats H as a symmetric Hessian (real ordered eigenvalues, orthogonal eigendecomposition on p.19); the ordering is a labelling
--   - encoding: x* the unique optimal solution, f* = f(x*) → x* any minimizer of f (∀ z, f x* ≤ f z), f* = f(x*); reason: strong convexity makes the minimizer unique; same instances
--   - encoding: (29): ∇f(x) = H(x−x*) + D(x)(x−x*), ‖D(x)‖ ≤ R_D‖x−x*‖ → ‖∇f(x) − H(x−x*)‖ ≤ R_D‖x−x*‖²; reason: equivalent: take D(x) = (∇f(x) − H(x−x*))(x−x*)ᵀ/‖x−x*‖²; the bound also makes H the derivative of ∇f at x*
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, proof of Theorem 1, p.17 (used in the proof of Theorem 2, p.20)

import Mathlib
import Definitions.Def_VRAccelCLT_SmoothStronglyConvex
import Definitions.Def_VRAccelCLT_Assumption2i

namespace VRAccelCLT

/-- **The Hessian at the optimum has its spectrum in `[η, L]`.** Lei, Shanbhag,
arXiv:2006.07769v3, proof of Theorem 1, p.17: "Since H is the Hessian matrix of f(x) at x = x∗, by
Assumptions 1(i) and 1(ii), we conclude that H has eigenvalues λ1, · · · , λm that satisfy
0 < η ≤ λm ≤ λm−1 ≤ · · · ≤ λ2 ≤ λ1 ≤ L." (used again in the proof of Theorem 2, p.20).

Under Assumption 1 (i)–(ii), with `x∗` a minimizer of `f` and `H` the matrix of Assumption 2 (i),
`H` is symmetric and each of its (real) eigenvalues lies in `[η, L]`.

**Formalization Note.** Symmetry is part of the conclusion (the paper orders the eigenvalues on the
real line and diagonalizes `H` orthogonally, p.19); the eigenvalues are those of
`Matrix.IsHermitian.eigenvalues`. The ordering `λ_m ≤ ⋯ ≤ λ_1` is only a labelling and is not
stated. `0 < η` is part of `SmoothStronglyConvex`. -/
theorem hessian_spectrum {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (L η RD : ℝ)
    (xstar : EuclideanSpace ℝ (Fin m)) (H : Matrix (Fin m) (Fin m) ℝ)
    (hA1 : SmoothStronglyConvex f L η) (hmin : ∀ z, f xstar ≤ f z)
    (hA2 : Assumption2i f xstar H RD) :
    ∃ hH : H.IsHermitian, ∀ i, η ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ L := by sorry

end VRAccelCLT
