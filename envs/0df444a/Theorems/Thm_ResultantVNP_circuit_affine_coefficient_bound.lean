-- Prove2me | Theorems.Thm_ResultantVNP_circuit_affine_coefficient_bound
-- name    : ResultantVNP.circuit_affine_coefficient_bound
-- status  : Proved
-- author  : @gjindal
-- created : 2026-11-14T10:53:12.893217+00:00
-- url     : https://prove2.me/theorems/8993dd2c-1b6b-4971-8e88-e8fd455983ab
-- title:
--   Circuit bound for coefficients after affine substitution
-- statement:
--   Let $C$ be an arithmetic circuit over $\mathbb C$, let $S$ be its number of addition and multiplication gates, and let $\delta_x\in\mathbb C$ be fixed for each input variable $x$. For every integer $s\ge0$, there is an arithmetic circuit $D$ satisfying
--
--   $$D(\mathbf x)=[z^s]C((\delta_x+zx)_{x}),\qquad \operatorname{size}(D)\le 2(s+1)^2S+1.$$
--
--   The bound is independent of the total degree of the polynomial computed by $C$. This provides the coefficient-extraction step used to pass from tensor determinant circuits to characteristic coefficient circuits.
--
--   **Formalization Note** Circuits count arithmetic gates only; variable and constant leaves have zero cost. Arbitrary shared intermediate results are allowed.
-- source:
--   Derived explicit circuit bound for the homogenization step in Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission #1103, proof of Theorem 1.4, p.17. The paper cites Strassen homogenization; this auxiliary statement supplies a direct constructive bound. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1103.pdf

import Mathlib
import Definitions.Def_ResultantVNP_Circuit

theorem ResultantVNP.circuit_affine_coefficient_bound {σ : Type} (C : ResultantVNP.Circuit σ) (δ : σ → ℂ) (s : ℕ) :
    ∃ D : ResultantVNP.Circuit σ,
      D.value = (MvPolynomial.aeval (fun x =>
        Polynomial.C (MvPolynomial.C (δ x)) +
          Polynomial.X * Polynomial.C (MvPolynomial.X x)) C.value).coeff s ∧
      D.size ≤ 2 * (s+1)^2 * C.size + 1 := by sorry
