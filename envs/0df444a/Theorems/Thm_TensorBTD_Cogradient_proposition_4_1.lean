-- Prove2me | Theorems.Thm_TensorBTD_Cogradient_proposition_4_1
-- name    : TensorBTD.Cogradient.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:28.34129+00:00
-- url     : https://prove2.me/theorems/660479ee-738b-43f2-bd49-4a53b9f28191
-- title:
--   Proposition 4.1, (4.3a), p. 7 — vec(C^(q)E)ᵀ = vec(C^(q))ᵀF^(q) and ∂/∂C^(q) = ∂/∂A^(P+q)·Eᵀ
-- statement:
--   Let $F^{(q)}=E\otimes\mathbb I_{I_{P+q}}$, the Kronecker product of the $R\times R'$ matrix $E$ with the identity of order $I_{P+q}$. Then:
--   1. for every $C^{(q)}\in\mathbb C^{I_{P+q}\times R}$,
--   $$\operatorname{vec}(C^{(q)}E)^{\mathrm T}=\operatorname{vec}(C^{(q)})^{\mathrm T}F^{(q)};$$
--   2. (chain rule (4.3a)) let $g$ be a complex-valued function of the factor matrices $A^{(1)},\dots,A^{(N)}$ of the unstructured CPD, and let $z$ be the structured unknowns. If $g$ is real-differentiable at the factor matrices (3.6) of $z$, then the cogradient of $z\mapsto g(A^{(1)},\dots,A^{(P)},C^{(1)}E,\dots,C^{(Q)}E)$ with respect to $C^{(q)}$ is
--   $$\frac{\partial}{\partial C^{(q)}}=\frac{\partial}{\partial A^{(P+q)}}\cdot E^{\mathrm T},$$
--   the right-hand side being the cogradient of $g$ with respect to $A^{(P+q)}$ evaluated at $A^{(P+q)}=C^{(q)}E$.
--
--   The proposition lets one first differentiate with respect to $A^{(P+q)}$ as if it were unstructured and then transfer to $C^{(q)}$; it gives (4.5b) from (4.5a).
--
--   **Formalization Note.** `vec` is column-major (index (column, row), Mathlib's `Matrix.vec`) and $\otimes$ is Mathlib's Kronecker product, whose row and column pairs are ordered as in Definition 2.9. The hypothesis that $g$ is real-differentiable (Fréchet, over $\mathbb R$) at the point is the presupposition of "applying the chain rule"; without it the identity can fail because `deriv` returns $0$ at non-differentiable points. Every function the mission applies it to (in particular $f$) is a polynomial in the real and imaginary parts and satisfies it. The Jacobian form (4.3b) is not stated here.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 7, Proposition 4.1, (4.3a)

import Mathlib
import Definitions.Def_TensorBTD_Cogradient_Setting

namespace TensorBTD.Cogradient

open Matrix

/-- Proposition 4.1, p. 7, with (4.3a): `vec(C^(q) E)ᵀ = vec(C^(q))ᵀ F^(q)` for
`F^(q) = E ⊗ 𝕀_{I_(P+q)}`, and the chain rule `∂/∂C^(q) = ∂/∂A^(P+q) · Eᵀ` for the cogradient of
a function `g` of the unstructured factor matrices, real-differentiable at the point, composed with
`A^(P+q) = C^(q) E`. -/
theorem proposition_4_1 {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} :
    (∀ (q : Fin Q) (C : Matrix (Fin (I (.inr q))) (Fin R) ℂ),
      vec (C * TensorBTD.Gramian.E L) = vecMul (vec C) (kronecker (TensorBTD.Gramian.E L) (1 : Matrix (Fin (I (.inr q))) (Fin (I (.inr q))) ℂ))) ∧
    ∀ (g : (TensorBTD.Gramian.GIdx I L → ℂ) → ℂ) (z : TensorBTD.Gramian.Unk I L → ℂ), DifferentiableAt ℝ g (TensorBTD.Gramian.fullVec z) →
      ∀ q : Fin Q, cogradC (g ∘ TensorBTD.Gramian.fullVec) z q = cogradMatG g (TensorBTD.Gramian.fullVec z) (.inr q) * (TensorBTD.Gramian.E L)ᵀ := by sorry

end TensorBTD.Cogradient
