-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlace_order_semilocalMultiplier_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.directFactorPlace_order_semilocalMultiplier_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:05.796951+00:00
-- url     : https://prove2.me/theorems/18676db8-6d3c-43bd-8201-186adbe0e835
-- title:
--   Direct Factor Semilocal Logarithmic Residue: direct Factor Place order semilocal Multiplier eq one
-- statement:
--   A semilocal multiplier with principal ideal `P * J`, where the complement
--   is coprime to the extended base prime, has normalized order one at `P`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L56-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L56-L114

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalLogarithmicResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_38
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue._p2m_local_instance_af27c6fddd_48
open DirectIntegralDifferentialResidue DirectFactorTraceResidue

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.directFactorPlace_order_semilocalMultiplier_eq_one
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    GlobalPlace.order
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (algebraMap (B k F) F t) = 1 := by sorry
