-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectFactorTraceResidue_directIntegralTrace_residue_eq_sum_directFactorTraces
-- name    : QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directIntegralTrace_residue_eq_sum_directFactorTraces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:44:41.078704+00:00
-- url     : https://prove2.me/theorems/c4028d68-56d6-450c-a6ff-4544c0f5eeb5
-- title:
--   Direct Factor Trace Residue: direct Integral Trace residue eq sum direct Factor Traces
-- statement:
--   Reduction of the direct integral trace equals the finite sum of the
--   actual traced normalized logarithmic residues at all upper factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L193-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorTraceResidue.lean#L193-L209

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directFactorTraceResidue_constantAlgebra
attribute [local instance] directFactorTraceResidue_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue._p2m_local_instance_49470eb06b_49
open DirectIntegralDifferentialResidue DirectFactorResidueTransport

theorem QEC.Coding.AlgebraicGeometry.DirectFactorTraceResidue.directIntegralTrace_residue_eq_sum_directFactorTraces
    (p : IsDedekindDomain.HeightOneSpectrum (R k)) (b : B k F) :
    algebraMap (R k) p.asIdeal.ResidueField
        (Algebra.intTrace (R k) (B k F) b) =
      ∑ P : (factors
          (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset,
        directFactorPlaceTrace k F p P
          (Differential.simplePoleResidue (k := k) (F := F)
            (AffinePlace.globalPlace k F (directFactorPlace k F p P))
            (directIntegralLogarithmicDifferentialAtSimplePole k F p P b)) := by sorry
