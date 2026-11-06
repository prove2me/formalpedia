-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_canonicalDivisor_degree_of_constantAlgebra_eq
-- name    : QEC.Coding.AlgebraicGeometry.canonicalDivisor_degree_of_constantAlgebra_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:35:29.286512+00:00
-- url     : https://prove2.me/theorems/439199ed-3af6-472a-b8c8-31083602cb14
-- title:
--   Algebraic Geometry: canonical Divisor degree of constant Algebra eq
-- statement:
--   The Algebraic Geometry construction uses the canonical Divisor degree of constant Algebra eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L14-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureGenus.lean#L14-L28

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry

theorem QEC.Coding.AlgebraicGeometry.canonicalDivisor_degree_of_constantAlgebra_eq
    (k F : Type*) [Field k] [Finite k] [Field F]
    [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
    [κ : Algebra k F] [IsScalarTower k (RatFunc k) F]
    [@IsFullConstantField k F _ _ (@AffinePlace.constantAlgebra k F _ _ π)]
    (hκ : κ = @AffinePlace.constantAlgebra k F _ _ π)
    {D : Divisor (GlobalPlace k F)}
    (hD : FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F) D) :
    Divisor.degree (GlobalPlace.residueDegree (κ := κ)) D =
      2 * (GlobalPlace.functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ) - 2 := by sorry
