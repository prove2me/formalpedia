-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectSemilocalUniformizer_directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
-- name    : QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:46.33925+00:00
-- url     : https://prove2.me/theorems/8b44584f-849e-4ac4-856f-4568f6bc4c6e
-- title:
--   Direct Semilocal Uniformizer: direct Factor Place order semilocal Multiplier eq zero of ne
-- statement:
--   A multiplier isolating `P` is a unit at every distinct factor `Q` over
--   the same direct prime, so its normalized order at `Q` is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalUniformizer.lean#L48-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/SemilocalUniformizer.lean#L48-L122

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SemilocalUniformizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer
open scoped Polynomial RatFunc nonZeroDivisors BigOperators
open UniqueFactorizationMonoid
open DirectIntegralDifferentialResidue
open DirectFactorSemilocalLogarithmicResidue
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer._p2m_local_instance_46770e045f_42

theorem QEC.Coding.AlgebraicGeometry.DirectSemilocalUniformizer.directFactorPlace_order_semilocalMultiplier_eq_zero_of_ne
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P Q : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (hQP : Q ≠ P)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p Q))
        (algebraMap (B k F) F t) = 0 := by sorry
