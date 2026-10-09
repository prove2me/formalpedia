-- Prove2me | Theorems.Thm_WeilDefect_MarkerStability_finite_gram_posSemidef_iff_nonnegative
-- name    : WeilDefect.MarkerStability.finite_gram_posSemidef_iff_nonnegative
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T21:07:52.272341+00:00
-- url     : https://prove2.me/theorems/c3ae37a0-a6b5-4b38-b3f3-d4c977b49858
-- title:
--   Finite Gram PSD tests a self-adjoint operator with nonnegative scalar complement
-- statement:
--   For a continuous self-adjoint operator A on a complete complex inner-product space, a finite column family u and a nonnegative real δ, suppose A z = δ z for every vector orthogonal to all columns. Then the finite matrix with entries inner(u_i,A u_j) is positive semidefinite exactly when A is nonnegative. No linear independence, invertibility, positive δ, or strict gap is assumed. Empty and singular column families are included.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/FiniteGram.lean and WeilDefect/Connes/FiniteCertificateGram.lean at compiling source head df7cd5371e1778aa18f13856f32247a971f62d6b

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

theorem WeilDefect.MarkerStability.finite_gram_posSemidef_iff_nonnegative
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Fintype I] (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (u : I → H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hshell : ∀ z : H, (∀ i : I, ⟪u i, z⟫_ℂ = 0) → A z = δ • z) :
    Matrix.PosSemidef (fun i j => ⟪u i, A (u j)⟫_ℂ) ↔ 0 ≤ A := by sorry
