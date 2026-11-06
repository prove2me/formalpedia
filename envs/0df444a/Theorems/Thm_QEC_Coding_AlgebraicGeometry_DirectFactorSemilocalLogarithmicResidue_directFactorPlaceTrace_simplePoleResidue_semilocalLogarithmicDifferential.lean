-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:49.270961+00:00
-- url     : https://prove2.me/theorems/eba29956-80e7-4e74-a445-7d5301c9a939
-- title:
--   Direct Factor Semilocal Logarithmic Residue: direct Factor Place Trace simple Pole Residue semilocal Logarithmic Differential
-- statement:
--   For a supplied semilocal principal factorization, the base-field trace of
--   the normalized local residue is exactly the chosen factor-residue trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L134-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L134-L157

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (J : Ideal (B k F))
    (hcop : IsCoprime
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal) J)
    (t : B k F) (ht : t ≠ 0) (b : B k F)
    (hspan : Ideal.span ({t} : Set (B k F)) =
      (P : Ideal (B k F)) * J) :
    directFactorPlaceTrace k F p P
        (Differential.simplePoleResidue (k := k) (F := F)
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (directFactorSemilocalLogarithmicDifferentialAtSimplePole
            k F p P t ht b)) =
      Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
