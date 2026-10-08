-- Prove2me | Theorems.Thm_RhinViola_final_polynomials_covariant
-- name    : RhinViola.final_polynomials_covariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T21:26:36.288453+00:00
-- url     : https://prove2.me/theorems/c1052d60-baea-4171-9730-cd682a695bae
-- title:
--   Rhin–Viola fourth-case polynomial covariances under the order-five birational transformation
-- statement:
--   With τ(x,y)=((1-x)/(1-xy),1-xy) and x,y complex satisfying 1-xy≠0, define the factored polynomials Q, R and S exactly as in Section 6.2, fourth case, of Rhin and Viola (1993). Their covariance identities are (1-xy)^2 Q(τ(x,y))=x^2 Q(x,y), (1-xy)^6 R(τ(x,y))=x^6 R(x,y), and (1-xy)^2 S(τ(x,y))=x^2 S(x,y). These polynomial identities support the algebraic invariance of the rational integrands in the ζ(2) irrationality measure proof. The statement exposes all polynomial factors explicitly, and all divisions are legitimate under the stated hypothesis.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Ann. Inst. Fourier 43 (1993), Section 6.1 formula (1) p. 99, and Section 6.2 fourth-case factorizations pp. 100–103; https://www.numdam.org/article/AIF_1993__43_1_85_0.pdf. Symbolically verified via SymPy rational cancellation on 4 October 2026. Relevant to Prove2Me parent PiIrrationality.rhin_viola_bound (bda7f199-9603-4c9e-8825-e30a14d70f09); no published dependency edge.

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem RhinViola.final_polynomials_covariant
    (x y : ℂ) (hxy : 1 - x * y ≠ 0) :
    (let Q : ℂ → ℂ → ℂ := fun u v =>
        (2 * u - 1) * (2 * v - 1) * (2 * u * v - 1) *
          (1 - 2 * u + u * v) * (1 - 2 * v + u * v);
     let R : ℂ → ℂ → ℂ := fun u v =>
        ((u - v) * (1 - 2 * u + u ^ 2 * v) *
          (1 - 2 * v + u * v ^ 2) * (1 - u - u * v) *
          (1 - v - u * v)) ^ 2;
     let S : ℂ → ℂ → ℂ := fun u v =>
        (3 * u - 2) * (3 * v - 2) * (3 * u * v - 1) *
          (1 - 3 * u + 2 * u * v) * (1 - 3 * v + 2 * u * v);
     let ξ : ℂ := (1 - x) / (1 - x * y);
     let η : ℂ := 1 - x * y;
     (η ^ 2 * Q ξ η = x ^ 2 * Q x y) ∧
       (η ^ 6 * R ξ η = x ^ 6 * R x y) ∧
       (η ^ 2 * S ξ η = x ^ 2 * S x y)) := by sorry
