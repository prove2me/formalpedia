-- Prove2me | Theorems.Thm_WeingartenCalc_Fundamental_projection_factorization
-- name    : WeingartenCalc.Fundamental.projection_factorization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:56.237458+00:00
-- url     : https://prove2.me/theorems/27689478-68bb-4a28-bae7-3ebeb4ed6199
-- title:
--   Section 2, p. 4 — the orthogonal projection onto the span of independent columns is $P=A(A^*A)^{-1}A^*$
-- statement:
--   Let $n$ be a finite index set and let $a_1,\dots,a_m\in\mathbb{C}^n$ be linearly independent. Let $A$ be the $n\times m$ matrix whose $x$-th column is $a_x$, i.e. $A_{ix}=\langle e_i,a_x\rangle$, and let $A^*$ be its conjugate transpose. If $P$ is an $n\times n$ complex matrix which is selfadjoint ($P^*=P$), idempotent ($P^2=P$), and whose image is $\operatorname{span}\{a_1,\dots,a_m\}$, then
--
--   $$P=A\,(A^*A)^{-1}A^*.$$
--
--   This is the matrix-analysis formula for the orthogonal projection onto the column space of $A$, the multidimensional version of the formula $vv^*/(v^*v)$ for the projection onto a line. Applied to the Haar average $P$ and a basis of the invariant tensors, it gives $P=AWA^*$ with the Weingarten matrix $W=(A^*A)^{-1}$.
--
--   **Formalization Note** The statement is general linear algebra over an arbitrary finite index type `n`; `(Aᴴ * A)⁻¹` is Mathlib's matrix inverse, which is a genuine inverse here because linear independence makes the Gram matrix $A^*A$ invertible. The cases $m=0$ (both sides zero) are included.
-- source:
--   Collins, Matsumoto & Novak, The Weingarten Calculus, arXiv:2109.14890v1, p. 4, Section 2 ("Then we have the matrix factorization P = A(A∗A)−1A∗")

import Mathlib
import Definitions.Def_WeingartenCalc_Fundamental_TensorPower

open MeasureTheory Matrix

namespace WeingartenCalc.Fundamental

theorem projection_factorization
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ} (a : Fin m → (n → ℂ))
    (ha : LinearIndependent ℂ a) (P : Matrix n n ℂ) (hPh : Pᴴ = P) (hPP : P * P = P)
    (hrange : LinearMap.range P.mulVecLin = Submodule.span ℂ (Set.range a)) :
    P = coordMatrix a * ((coordMatrix a)ᴴ * coordMatrix a)⁻¹ * (coordMatrix a)ᴴ := by sorry

end WeingartenCalc.Fundamental
