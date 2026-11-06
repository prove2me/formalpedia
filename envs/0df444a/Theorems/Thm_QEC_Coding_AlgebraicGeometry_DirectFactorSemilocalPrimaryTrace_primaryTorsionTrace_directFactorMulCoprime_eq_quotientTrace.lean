-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalPrimaryTrace_primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:15.258685+00:00
-- url     : https://prove2.me/theorems/d3f3c2e5-e7eb-44b1-afd7-0ba721de7396
-- title:
--   Direct Factor Semilocal Primary Trace: primary Torsion Trace direct Factor Mul Coprime eq quotient Trace
-- statement:
--   A coprime semilocal complement contributes no primary trace, so the
--   product quotient has exactly the ordinary multiplication trace on the chosen
--   upper factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalPrimaryTrace.lean#L54-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalPrimaryTrace.lean#L54-L85

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorPrimaryTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CoprimeQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimaryTorsion_CRTTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorSemilocalPrimaryTrace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace._p2m_local_instance_de14ef7384_45
open DirectFactorPrimaryTrace

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalPrimaryTrace.primaryTorsionTrace_directFactorMulCoprime_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    primaryTorsionTrace p.asIdeal
        (Algebra.lmul (R k) (B k F ⧸ ((P : Ideal (B k F)) * J))
          (Ideal.Quotient.mk ((P : Ideal (B k F)) * J) b)) depth =
      Algebra.trace (R k ⧸ p.asIdeal)
        (B k F ⧸ (P : Ideal (B k F)))
        (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by sorry
