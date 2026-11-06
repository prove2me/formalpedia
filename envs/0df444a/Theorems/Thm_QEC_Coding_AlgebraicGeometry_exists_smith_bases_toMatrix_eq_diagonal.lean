-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal
-- name    : QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:46:05.496508+00:00
-- url     : https://prove2.me/theorems/dec26154-9b0b-4e05-8d9c-96bb97e33e78
-- title:
--   Algebraic Geometry: exists smith bases to Matrix eq diagonal
-- statement:
--   An injective endomorphism of a finite free module over a principal ideal
--   domain is diagonal between suitable source and target bases, and every
--   diagonal coefficient is nonzero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialSmithMatrix.lean#L32-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialSmithMatrix.lean#L32-L66

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
variable {R M : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal {n : ℕ}
    (b : Basis (Fin n) R M) (f : M →ₗ[R] M)
    (hf : Function.Injective f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a := by sorry
