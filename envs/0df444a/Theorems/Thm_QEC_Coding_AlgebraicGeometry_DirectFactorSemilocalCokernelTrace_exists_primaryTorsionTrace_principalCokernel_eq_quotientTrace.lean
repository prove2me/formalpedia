-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalCokernelTrace_exists_primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.exists_primaryTorsionTrace_principalCokernel_eq_quotientTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:55.568352+00:00
-- url     : https://prove2.me/theorems/675db1a2-1b13-42d1-9c85-067b15b7f6a6
-- title:
--   Direct Factor Semilocal Cokernel Trace: exists primary Torsion Trace principal Cokernel eq quotient Trace
-- statement:
--   A semilocal multiplier exists for which the principal-cokernel primary
--   trace is exactly the ordinary multiplication trace on the chosen factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalCokernelTrace.lean#L105-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalCokernelTrace.lean#L105-L121

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalCokernelTrace.exists_primaryTorsionTrace_principalCokernel_eq_quotientTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) (depth : ℕ) (hdepth : 0 < depth) :
    ∃ t : B k F, t ≠ 0 ∧
      primaryTorsionTrace p.asIdeal
          (principalCokernelMul (R := R k) t b) depth =
        Algebra.trace (R k ⧸ p.asIdeal)
          (B k F ⧸ (P : Ideal (B k F)))
          (Ideal.Quotient.mk (P : Ideal (B k F)) b) := by sorry
