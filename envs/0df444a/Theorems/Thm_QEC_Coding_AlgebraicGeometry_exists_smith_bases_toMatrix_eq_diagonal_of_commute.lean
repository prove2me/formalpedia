-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_exists_smith_bases_toMatrix_eq_diagonal_of_commute
-- name    : QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:41:41.840492+00:00
-- url     : https://prove2.me/theorems/802ea026-1e81-4239-884c-80dc317f82aa
-- title:
--   Algebraic Geometry: exists smith bases to Matrix eq diagonal of commute
-- statement:
--   The Smith bases can be chosen so that every endomorphism commuting with
--   the injective endomorphism has the same diagonal entries in the source and
--   target bases.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialSmithMatrix.lean#L71-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/PolynomialSmithMatrix.lean#L71-L89

import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialSmithMatrix
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Module
variable {R M : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M]

theorem QEC.Coding.AlgebraicGeometry.exists_smith_bases_toMatrix_eq_diagonal_of_commute {n : ℕ}
    (b : Basis (Fin n) R M) (f g : M →ₗ[R] M)
    (hf : Function.Injective f) (hcomm : f.comp g = g.comp f) :
    ∃ source target : Basis (Fin n) R M, ∃ a : Fin n → R,
      (∀ i, a i ≠ 0) ∧
        LinearMap.toMatrix source target f = Matrix.diagonal a ∧
          ∀ i, LinearMap.toMatrix source source g i i =
            LinearMap.toMatrix target target g i i := by sorry
