-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorSemilocalLogarithmicResidue_exists_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential_eq_factorResidueTrace
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.exists_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential_eq_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:49.980948+00:00
-- url     : https://prove2.me/theorems/ecef336d-d158-4fbc-bb0d-db255adde770
-- title:
--   Direct Factor Semilocal Logarithmic Residue: exists direct Factor Place Trace simple Pole Residue semilocal Logarithmic Differential eq factor Residue Trace
-- statement:
--   There is an actual semilocal multiplier of order one whose logarithmic
--   simple-pole residue realizes the chosen factor-residue trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L161-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorSemilocalLogarithmicResidue.lean#L161-L184

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

theorem QEC.Coding.AlgebraicGeometry.DirectFactorSemilocalLogarithmicResidue.exists_directFactorPlaceTrace_simplePoleResidue_semilocalLogarithmicDifferential_eq_factorResidueTrace
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors
      (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    ∃ t : B k F, ∃ ht : t ≠ 0,
      GlobalPlace.order
          (AffinePlace.globalPlace k F (directFactorPlace k F p P))
          (algebraMap (B k F) F t) = 1 ∧
        directFactorPlaceTrace k F p P
            (Differential.simplePoleResidue (k := k) (F := F)
              (AffinePlace.globalPlace k F (directFactorPlace k F p P))
              (directFactorSemilocalLogarithmicDifferentialAtSimplePole
                k F p P t ht b)) =
          Ideal.Factors.factorResidueTrace p.asIdeal P b := by sorry
