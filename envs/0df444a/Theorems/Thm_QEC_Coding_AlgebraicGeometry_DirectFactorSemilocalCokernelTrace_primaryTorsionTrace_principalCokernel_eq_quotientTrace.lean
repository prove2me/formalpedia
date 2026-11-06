-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalCokernelTrace_primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:00.148764+00:00
-- url     : https://prove2.me/theorems/4422ea27-c07c-403a-9d0e-c0c2d9406067
-- title:
--   Direct Factor Semilocal Cokernel Trace: primary Torsion Trace principal Cokernel eq quotient Trace
-- statement:
--   If the principal multiplier ideal is one chosen upper factor times a
--   base-primary-coprime complement, its induced cokernel multiplication has
--   primary trace equal to the ordinary quotient trace on that factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalCokernelTrace.lean#L53-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalCokernelTrace.lean#L53-L79

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalMultiplier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrincipalCokernelTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalCokernelTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace._p2m_local_instance_d1e0a01c5a_46

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.primaryTorsionTrace_principalCokernel_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J)
    (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (principalCokernelMul (R := R k) t b) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by sorry
