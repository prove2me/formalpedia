-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectIntegralDifferentialResidue_simplePoleResidue_directIntegralLogarithmicDifferential
-- name    : QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.simplePoleResidue_directIntegralLogarithmicDifferential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:37:29.41514+00:00
-- url     : https://prove2.me/theorems/54da047c-79ec-4afa-afc6-435ff789ae56
-- title:
--   Direct Integral Differential Residue: simple Pole Residue direct Integral Logarithmic Differential
-- statement:
--   The normalized residue of the integral multiple of the base logarithmic
--   differential is its actual reduced coefficient times the genuine
--   ramification index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialResidue.lean#L165-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralDifferentialResidue.lean#L165-L181

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_37
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_39
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue._p2m_local_instance_3e6bb6d2a4_49

theorem QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialResidue.simplePoleResidue_directIntegralLogarithmicDifferential
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset)
    (b : B k F) :
    Differential.simplePoleResidue (k := k) (F := F)
        (AffinePlace.globalPlace k F (directFactorPlace k F p P))
        (directIntegralLogarithmicDifferentialAtSimplePole k F p P b) =
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residue
          (directIntegralToValuationRing k F p P b) *
        (p.asIdeal.ramificationIdx' (P : Ideal (B k F)) :
          (AffinePlace.globalPlace k F
            (directFactorPlace k F p P)).residueField) := by sorry
